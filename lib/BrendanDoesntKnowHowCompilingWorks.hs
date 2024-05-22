module Basics where

import Control.Monad.State
import Data.Maybe
import Data.Functor.Identity
import Data.List
import qualified Data.Map.Strict as Map


-- utility for checking if a list has duplicates
allUnq:: Eq a => [a] -> Bool
allUnq = f []
    where
        f seen (x:xs) = x `notElem` seen && f (x:seen) xs
        f _ [] = True

-- l is the type of our alphabet (most likely a finite set),
-- s is the type of our states
-- Maybe l because we allow empty transitions
data AutData l s = AD { stateData :: [s] 
                      , acceptData :: [s] 
                      , transitionData :: [(s, [(Maybe l, s)])] }
                      deriving Show

-- recall:
-- "State s Bool" is "s -> (Bool,s)"
data DetAut  l s = DA { states :: [s]
                      , accept :: [s]
                      , delta :: l -> State s Bool }

-- a typeclass for finite alphabets
class Alphabet a where
  alphIter :: [a] -> Bool
-- alphIter should check if the list contains exactly the elements of the type


-- just a b c for now
data Letter = A | B | C deriving (Eq, Ord)
instance Show Letter where
  show A = "a"
  show B = "b"
  show C = "c"

instance Alphabet Letter where
  alphIter ls = sort ls == [A,B,C] 
  
-- data Letter = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

-- can the data define a det automaton? (totality of transition)
detCheck :: (Alphabet l, Eq l, Eq s) => AutData l s -> Bool
detCheck ad = length sts == length (stateData ad) && allUnq sts  -- all states are in transitionData exactly once
              && all detCheckHelper stateTrs where               -- check transitions for each letter exactly once
  sts = map fst $ transitionData ad
  stateTrs = map snd $ transitionData ad

detCheckHelper :: (Alphabet l, Eq l, Eq s) => [(Maybe l,s)] -> Bool
detCheckHelper trs = notElem Nothing (map fst trs)            -- no empty transitions
                     && alphIter (map fromJust (map fst trs)) -- transition set is exactly the alphabet

-- contingent on passing safetyCheck, make data into a DA
encodeDA :: (Alphabet l, Eq l, Eq s) => AutData l s -> Maybe (DetAut l s)
encodeDA d | not $ detCheck d = Nothing
           | otherwise = Just $ DA { states = stateData d
                                   , accept = acceptData d
                                   , delta = StateT . stTrans } where
               stTrans l s = return (calcV l s, calcS l s)
               calcV l s = calcS l s `elem` acceptData d
               calcS l s = fromJust $ lookup (Just l) $ fromJust (lookup s (transitionData d)) 

-- takes DA, input letter list, and initial state to output pair
run :: DetAut l s -> [l] -> s -> (Bool, s)
run da w s0 = (`runState` s0) $ foldl' (>>) (pure False) (map (delta da) w) 

autAccept :: DetAut l s -> [l] -> s -> Bool
autAccept da w s0 = fst $ run da w s0

finalState :: DetAut l s -> [l] -> s -> s
finalState da w s0 = snd $ run da w s0

-- NA definitions

-- "StateT s [] Bool" is "s -> [(Bool,s)]"
data NDetAut l s = NA { nstates :: [s]
                      , naccept :: [s]
                      , ndelta :: Maybe l -> StateT s [] Bool }


-- make data into an NA (no need for safety check)
encodeNA :: AutData l s -> NDetAut l s
encodeNA d = NA { nstates = stateData d
                , naccept = acceptData d
                , ndelta = undefined }

-- REGEX definitions 

data Regex l = Empty | 
               Epsilon |
               L l | 
               Alt (Regex l) (Regex l) |
               Seq (Regex l) (Regex l) | 
               Star (Regex l)
  deriving (Eq) 

instance Show l => Show (Regex l) where
  show Empty = "EmptySet"
  show Epsilon = "Epsilon"
  show (L a) = show a
  show (Star (Alt r r')) = "(" ++ (show r) ++ " + " ++ (show r') ++ ")*"
  show (Alt r r') = "(" ++ (show r) ++ " + " ++ (show r') ++ ")"
  show (Seq r r') = (show r) ++ (show r')
  show (Star r) = "(" ++ (show r) ++ ")*"

-- very simple regex simplifications (guaranteed to terminate or your money back)
simplifyRegex :: Eq l => Regex l -> Regex l
simplifyRegex rx = case rx of
                    (Alt Empty r) -> simplifyRegex r
                    (Alt r Empty) -> simplifyRegex r
                    (Alt r r') | r == r' -> simplifyRegex r
                    (Seq r Epsilon) -> simplifyRegex r
                    (Seq Epsilon r) -> simplifyRegex r
                    (Seq _ Empty) -> Empty
                    (Seq Empty _) -> Empty
                    (Star Empty) -> Empty
                    (Star Epsilon) -> Epsilon
                    (Star (Star r)) -> simplifyRegex $ Star r
                    (Star (Alt Empty r)) -> simplifyRegex r
                    (Star (Alt r Empty)) -> simplifyRegex r
                    (Star (Seq Epsilon r)) -> simplifyRegex r
                    (Star (Seq r Epsilon)) -> simplifyRegex r
                    x -> x

-- REGEX to DetAut
-- Since regex to automata inducts on the transition functions, we need a way to glue or reshape our automata nicely
-- As we add more states we need to relable them. The base states are 1 and 2, multiplying by 3 is sequence, multiplying by 5 and 7 is Alt, multiplying by 11 is Star

--useful function to glue states together
transForState :: Eq s => AutData l s -> s -> [(Maybe l, s)]
transForState aut s 
 | isNothing (lookup s (transitionData aut)) =[]
 | otherwise = fromJust (lookup s (transitionData aut))

-- For each operator we define two corresponding functions. One outputs the automata data associated with that operator, 
-- the other stitches and modifies the transition function across the inputs automata (mostly using Epsilon transitions)

regToAut :: Regex l -> (AutData l Int, Int) -- gives an integer automata and a starting state
regToAut (L l) = (AD [1,2] [2] [(1, [(Just l,2)]), (1, [(Just l,2)])], 1) 
regToAut Empty = (AD [1,2] [2] [], 1)
regToAut Epsilon = (AD [1,2] [2] [(1, [(Nothing, 2)])], 1)
regToAut (Seq a b) = seqRegAut  (regToAut a) (regToAut b)
regToAut (Alt a b) = altRegAut  (regToAut a) (regToAut b)
regToAut (Star a) = starRegAut $ regToAut a

seqRegAut :: (AutData l Int, Int) -> (AutData l Int, Int) -> (AutData l Int, Int)
seqRegAut (aut1,s1) (aut2,s2) = (AD ([x | x <- stateData aut1 ]++[x*3 | x <- stateData aut2])
                                    [3*x | x <- acceptData aut2] 
                                    (gluingSeq (aut1, s1) (aut2, s2))
                                    , s2)


gluingSeq :: (AutData l Int, Int)->(AutData l Int, Int) -> [(Int, [(Maybe l, Int)])]
gluingSeq (aut1, s1) (aut2, s2) =  firstAut ++ middle ++secondAut where
 firstAut = [(x, transForState aut1 x) | x<- stateData aut1, x `notElem` acceptData aut1]
 middle = [(x, (transForState aut1 x)++[(Nothing, 3*s2)]) | x<- acceptData aut1]
 secondAut = [(x*3, multTuple 3 (transForState aut2 x)) | x<- stateData aut2]

altRegAut :: (AutData l Int, Int) -> (AutData l Int, Int) -> (AutData l Int, Int)
altRegAut (aut1, s1)  (aut2, s2) = (AD ([1,2]++[x*5| x<- stateData aut1]++[x*7| x<- stateData aut2])
                                [2] 
                                (gluingAlt (aut1, s1) (aut2, s2))
                                ,1)

gluingAlt :: (AutData l Int, Int)->(AutData l Int, Int) -> [(Int, [(Maybe l, Int)])]
gluingAlt (aut1,s1) (aut2,s2) = start ++ firstAut ++endFirstAut ++ secondAut ++ endSecondAut where
 start = [(1, [(Nothing, s1*5)]), (1, [(Nothing, s2*7)])]
 firstAut = [(x*5, multTuple 5 (transForState aut1 x) ) | x<- stateData aut1, x `notElem` acceptData aut1]
 secondAut = [(x*7, multTuple 7 (transForState aut2 x) ) | x<- stateData aut2, x `notElem` acceptData aut2]
 endFirstAut = [(x*5, (multTuple 5 (transForState aut1 x))++[(Nothing,2)] ) | x<- acceptData aut1]
 endSecondAut = [(x*7, (multTuple 7 (transForState aut2 x))++[(Nothing,2)] ) | x<- acceptData aut2]

starRegAut :: (AutData l Int, Int) -> (AutData l Int,Int)
starRegAut (aut, s) = (AD (1:[x*11 | x<- stateData aut])
                    [1]
                    (gluingStar (aut, s))
                    ,1)

gluingStar :: (AutData l Int, Int)-> [(Int, [(Maybe l, Int)])]
gluingStar (aut1, s1) = start ++ middle ++ end where
 start = [(1, [(Nothing, s1*11)])]
 middle = [(x, multTuple 11 (transForState aut1 x))| x<-stateData aut1, x `notElem` acceptData aut1]
 end = [(a, [(Nothing, 1)]++ multTuple 11 (transForState aut1 a)) | a <- acceptData aut1]

multTuple :: Int -> [(a,Int)] -> [(a,Int)]
multTuple _ [] = []
multTuple n ((a,b):xs) = (a,n*b):(multTuple n xs) 


-- Take a collection of data and starting states, outputs a regular expression which corresponds to the language.
autToReg :: Eq l =>Ord s =>(AutData l s, s)-> Regex l
autToReg (aut, s)= kleeneAlgo intAut 0 lastState lastState where 
 intAut = (fst.cleanAutomata.relableAut) (aut,s)
 lastState = (length (stateData intAut)-1) 
--autToReg aut [s]= kleeneAlgo newAut 0 (length stateData aut) (length stateData aut) where newAut = cleanAutomata . relableAut aut

--following the Wikipedia page, this function recursively removes elements and uses the removed transition lables to construct the regex. 
kleeneAlgo:: Eq l => AutData l Int -> Int -> Int -> Int -> Regex l
kleeneAlgo aut i j (-1) = simplifyRegex (if i==j then Alt Epsilon (altSet [if  isNothing a then Epsilon else L (fromJust a) | a <- successorSet aut i j]) else (altSet [if  isNothing a then Epsilon else L (fromJust a) | a <- successorSet aut i j]) )
kleeneAlgo aut i j k = (Alt (simplifyRegex(kleeneAlgo aut i j (k-1))) (simplifyRegex(seqSet [simplifyRegex(kleeneAlgo aut i k (k-1)), simplifyRegex (Star (kleeneAlgo aut k k (k-1))), simplifyRegex (kleeneAlgo aut k j (k-1)) ])))

-- takes some automata data and two states, s1, s2. Ouputs all the ways to get s2 from s1
successorSet :: Eq s => AutData l s -> s -> s -> [Maybe l]
successorSet aut s1 s2 
 | isNothing (lookup s1 (transitionData aut) ) = [] -- if there are no successors
 | otherwise = map fst (filter (\w -> s2 == snd w) (fromJust $ lookup s1 (transitionData aut)) )



altSet:: [Regex l]->Regex l
altSet [] = Empty
altSet [x] = x
altSet (x:xs) = Alt x (altSet xs)

seqSet:: [Regex l]->Regex l
seqSet [] = Empty
seqSet [x] = x
seqSet (x:xs) = Seq x (seqSet xs)

-- states as integer makes everything easier. We use a dictionary to relable in one sweep per say
relableHelp :: Ord s => AutData l s -> s -> Int
relableHelp aut s = fromJust (Map.lookup s (Map.fromList $ zip (stateData aut) [1 .. (length (stateData aut)+1)]))

relableAut :: Ord s => (AutData l s, s) -> (AutData l Int, Int)
relableAut (aut, s1) = (AD [relableHelp aut s | s <- stateData aut]
                           [relableHelp aut s| s<- acceptData aut]
                           [(relableHelp aut s, [ (a, relableHelp aut b)| (a,b) <- (transForState aut s)] ) | s<- stateData aut]
                       , relableHelp aut s1)


-- take aut data and make a nice start state/end state
cleanAutomata:: (AutData l Int, Int) -> (AutData l Int, Int)
cleanAutomata (aut, s) = (AD (0:lastState:(stateData aut) )
                          [lastState]
                          (cleanTransition (aut,s))
                         , 0) where lastState = 1+(length (stateData aut))
 
cleanTransition:: (AutData l Int, Int) -> [(Int, [(Maybe l, Int)])]
cleanTransition (aut, s) = start ++ middle ++ end where
 start = [(0, [(Nothing, s)])]
 middle = [(x, transForState aut x) | x <- stateData aut, x `notElem` acceptData aut]
 end = [(x, [(Nothing, (length $ stateData aut)+1)]++(transForState aut x)) | x<- acceptData aut]


 -- Examples

exampleAut :: AutData String Int
exampleAut = AD [1,2,3] [2] [(1, [(Just "a", 1), (Just "b", 2)]), (2, [(Just "b", 2), (Just "a", 3)   ]), (3, [(Just "a", 2), (Just "b", 2)])]

exampleAut2 :: AutData String Int
exampleAut2 = AD [1,2,3,4] [4] [(1, [(Just "a", 2)]), (2, [(Just "a", 3)]), (3, [(Just "a", 4)])]