\section{The most basic library}\label{sec:Basics}

This section describes a module which we will import later on.

\begin{code}
module Basics where

import Control.Monad.State
import Data.Maybe
import Data.Functor.Identity
import Data.List

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

data Regex l = Empty | Epsilon | L l | Alt (Regex l) (Regex l) | Seq (Regex l) (Regex l) | Star (Regex l) 

instance Eq l => Eq (Regex l) where
  (==) Empty Empty = True
  (==) Epsilon Epsilon = True
  (==) (L l) (L l') = l == l'
  (==) (Alt r r') (Alt r'' r''') = compsEq r r' r'' r'''
  (==) (Seq r r') (Seq r'' r''') = compsEq r r' r'' r'''
  (==) (Star r) (Star r') = r == r'
  -- where
  -- compsEq r r' r'' r''' = (r == r'' && r' == r''') || (r == r''' && r' == r'')

-- couldn't make the "where" notation work, but that would be preferable
compsEq :: Eq a => a -> a -> a -> a -> Bool
compsEq r r' r'' r''' = (r == r'' && r' == r''') || (r == r''' && r' == r'')

instance Show l => Show (Regex l) where
  show Empty = "EmptySet"
  show Epsilon = "Epsilon"
  show (L a) = show a
  show (Star (Alt r r')) = "(" ++ (show r) ++ " + " ++ (show r') ++ ")*"
  show (Alt r r') = "(" ++ (show r) ++ " + " ++ (show r') ++ ")"
  show (Seq r r') = (show r) ++ (show r')
  show (Star r) = "(" ++ (show r) ++ ")*"

simplifyRegex :: Eq l => Regex l -> Regex l
simplifyRegex rx = case rx of
                    (Alt Empty r) -> simplifyRegex r
                    (Alt r Empty) -> simplifyRegex r
                    (Alt r r') | r == r' -> simplifyRegex r
                    (Seq r Epsilon) -> simplifyRegex r
                    (Seq Epsilon r) -> simplifyRegex r
                    (Seq r Empty) -> Empty
                    (Seq Empty r) -> Empty
                    (Star Empty) -> Empty
                    (Star Epsilon) -> Epsilon
                    (Star (Star r)) -> simplifyRegex r
                    x -> x

-- REGEX to DetAut
-- Since regex to automata inducts on the transition functions, we need a way to glue or reshape our automata nicely
-- As we add more states we need to relable them. The base states are 1 and 2, multiplying by three is sequence, multiplying by 5 and 7 is Alt, multiplying by 11 is Star
regToAut :: Regex l -> AutData l Int
regToAut (L l) = AD [1,2] [2] [(1, [(Just l,2)]), (1, [(Just l,2)])] 
regToAut r = undefined
-- regToAut (Seq a b) = seqRegAut $ (regToAut a) (regToAut b)
-- regToAut (Alt a b) = altRegAut $ (regToAut a) (regToAut b)
-- regToAut (Star a) = starRegAut $ regToAut a

seqRegAut :: AutData l Int -> AutData l Int -> AutData l Int
seqRegAut = undefined
-- seqRegAut aut1 aut2 = AD [x | x <- stateData aut2 ]++[x*3 | x <- stateData aut2] [x | x <- acceptData] [(x*3, gluingStatesSeq x aut1 aut2 ) | x <- stateData aut1]

altRegAut :: AutData l Int -> AutData l Int -> AutData l Int
-- segRegAut aut1 aut2 = AD [1,2]++[x*5| x<- stateData aut1]++[x*7| x<- stateData aut2]
--                              [2] 
--                              [(1,[(Nothing, s*5,7)| s<- StartingState aut1,aut2])]++[(x*5,(Nothing,2)++multTuple 5 (fromJust (lookup x transitionData aut1)] | x<- acceptData aut1,aut2]++[(x*5,multTuple 5 (fromJust (lookup x transitionData aut1) | x<-stateData aut1,aut2, x `notElem` acceptData aut1,aut2]

starRegAut :: AutData l Int -> AutData l Int
-- starRegAut aut = AD [1]++[x*11 | x<- stateData aut]
--                     [1]
--                     [1, [(Nothing, s*11) | s<- StartingState]]++[(x*11,(Nothing, 1)++multTuple 11 (fromJust (lookup x transitionData aut)] | x<- acceptData aut1]++[(x*11,multTuple 5 (fromJust (lookup x transitionData aut) | x<-stateData aut, x `notElem` acceptData aut]

-- This function takes the first sequent and captures its original structure while updating the labels. The target states get connected by an empty transition to the
--starting states of the second sequent.
gluingStatesSeq :: Int -> AutData l Int -> AutData l Int -> AutData l Int
gluingStatesSeq  x aut1 aut2 = undefined
 -- | x `elem` acceptData aut1 = (multTuple 3 (fromJust  (lookup x transitionData aut1)))++(Nothing, StartingState)
 -- |otherwise  fromJust  multTuple 3 (lookup x transitionData aut1)

multTuple :: Int -> [(a,Int)] -> [(a,Int)]
multTuple _ [] = []
multTuple n (a,b):xs = (a,n*b):(multTuple n xs) 


-- Take a collection of data and starting state, outputs a regular expression which corresponds to the language.
autToReg :: Autdata l s -> [s] -> Regex
autToReg aut [s]= kleeneAlgo newAut 0 (length stateData aut) (length stateData aut) where newAut = cleanAutomata . relableAut aut

--following the Wikipedia page, this function recursively removes elements and uses the removed transition lables to construct the regex. 
kleeneAlgo:: AutData l Int -> Int -> Int -> Regex l
kleeneAlgo aut i j (-1) = if i==j then Alt Epsilon altSet [ l | l `elem` second fromJust (lookup i transitionData aut)] else altSet [ l | l `elem` second fromJust (lookup i transitionData aut)]
kleeneAlgo aut i j k = Alt (kleeneAlgo i j (k-1)) (seqSet [(kleeneAlgo i j (k-1)), Star (kleeneAlgo i j (k-1)), (kleeneAlgo i j (k-1)) ])


altSet:: [l]->Regex L
altSet [] = Epsilon
altSet (x:xs) = Seq x (seqSet xs)

-- states as integer makes everything easier 
relableAut :: Autdata l s -> Autdata l Int
relableAut aut = undefined

relableHelper :: [s]->[s]->[(s,[(Maybe l,s)])]->[Int]->[Int]->[(Int, [(Maybe l, Either s Int)])]->Int->[s]->[s]->[(s,[(Maybe l,s)])]->[Int]->[Int]->[(Int, [(Maybe l, Either s Int)])]
relableHelper :: _ [] _ _ _ _ _ = return yadayada
relableHelper acc (s:ss) trans intAcc intState intTrans n = do 
 let newIntState = n:intState
 let newN = n+1
 let newIntAcc = if s `elem` acc then n:intAcc else intAcc
 let newAcc = if s `elem` acc then filter (/= s) acc else acc
 let newIntTrans = undefined
 let newTrans = filter (\w -> (first w)==s) trans
 relableHelper newAcc ss newTrans newIntAcc newIntState newIntState newN

-- take aut data and make a nice start state/end state
cleanAutomata:: Autdata l Int -> s -> AutData l Int -> s
cleanAutomata aut s = AD length acceptData aut
                         0:(stateData aut)
                         [(w, if w `elem` acceptData aut then (Nothing, length acceptData aut):(fromJust (lookup w transitionData aut)) else fromJust (lookup w transitionData aut) ) | w <- stateData aut]++ [0,[(Nothing, x) | x<-s]]
                       
\end{code}

