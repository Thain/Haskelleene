\section{The most basic library}\label{sec:Basics}

This section describes a module which we will import later on.

\begin{code}
{-# LANGUAGE TupleSections #-}
module Basics where

-- import Control.Monad.State
import Data.Maybe
import Data.List

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.QuickCheck


-- utility for checking if a list has duplicates
allUnq:: Eq a => [a] -> Bool
allUnq = f []
    where
        f seen (x:xs) = x `notElem` seen && f (x:seen) xs
        f _ [] = True

getTrs :: (Eq a, Eq b) => [(a,[(b,a)])] -> a -> b -> [(b,a)]
getTrs allTrs s0 ltr = filter (\x -> fst x == ltr) $ filter (\x -> fst x == s0) allTrs >>= snd

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
                      , delta :: l -> s -> s }

-- a typeclass for finite alphabets
class Ord a => Alphabet a where
  completeList :: [a]

-- alphIter should check if the list contains exactly the elements of the type
alphIter :: Alphabet a => [a] -> Bool
alphIter l = sort l == completeList 

-- just a b c for now
data Letter = A | B | C deriving (Eq, Ord)

instance Show Letter where
  show A = "a"
  show B = "b"
  show C = "c"

instance Alphabet Letter where
  completeList = [A,B,C]
  -- data Letter = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

instance Arbitrary Letter where
  arbitrary = elements completeList

-- can the data define a det automaton? (totality of transition)
detCheck :: (Alphabet l, Eq s) => AutData l s -> Bool
detCheck ad = length sts == length (stateData ad) && allUnq sts 
              -- all states are in transitionData exactly once
              && all detCheckHelper stateTrs where              
              -- check transitions for each letter exactly once
  sts = fst <$> transitionData ad
  stateTrs = snd <$> transitionData ad

detCheckHelper :: (Alphabet l, Eq s) => [(Maybe l,s)] -> Bool
detCheckHelper trs = notElem Nothing (fst <$> trs)        
                     -- no empty transitions
                     && alphIter (fromJust . fst <$> trs) 
                     -- transition set is exactly the alphabet

-- contingent on passing safetyCheck, make data into a DA
encodeDA :: (Alphabet l, Eq s) => AutData l s -> Maybe (DetAut l s)
encodeDA d | not $ detCheck d = Nothing
           | otherwise = Just $ DA { states = stateData d
                                   , accept = acceptData d
                                   , delta = safeDelta } where
               safeDelta ltr st = fromJust $ lookup (Just ltr) $ fromJust (lookup st (transitionData d)) 

-- takes DA, input letter list, and initial state to output pair
run :: DetAut l s -> s -> [l] -> s
run _ s0 [] = s0
run da s0 (w:ws) = run da (delta da w s0) ws

acceptDA :: (Eq s) => DetAut l s -> s -> [l] -> Bool
acceptDA da s0 w = run da s0 w `elem` accept da

-- NA definitions

-- "StateT s [] Bool" is "s -> [(Bool,s)]"
data NDetAut l s = NA { nstates :: [s]
                      , naccept :: [s]
                      , ndelta :: Maybe l -> s -> [s] }

-- check the data can define an nondeterministic automaton:
ndetCheck :: (Alphabet l, Eq s) => AutData l s -> Bool
ndetCheck ad = allUnq sts &&
               -- all states are in transitionData exactly once
               all (\(st,trs) -> (Nothing,st) `notElem` trs) trdata
               -- no epsilon self-loop
  where trdata = transitionData ad 
        sts = fst <$> trdata

-- make data into an NA (no need for safety check)
encodeNA :: (Alphabet l, Eq s) => AutData l s -> Maybe (NDetAut l s)
encodeNA d | not $ ndetCheck d = Nothing
           | otherwise         = Just $
  NA { nstates = stateData d
     , naccept = acceptData d
     , ndelta = help }
  where help sym st = case lookup st (transitionData d) of
                        Nothing -> []
                        Just ls -> [ st' | (sym', st') <- ls, sym' == sym ]

-- put an NA back into autdata, e.g. to turn it into regex
decode :: (Alphabet l, Eq s) => NDetAut l s -> AutData l s
decode nda = AD { stateData = sts
                  , acceptData = naccept nda
                  , transitionData = trandata
                  }
  where sts = nstates nda
        ntrans = ndelta nda
        symlist = Nothing : (Just <$> completeList)
        trandata = graph help sts -- where ...
        help st = concatMap (\sym -> (sym,) <$> ntrans sym st) symlist
        graph f as = zip as $ f <$> as
-- graph :: (a -> b) -> [a] -> [(a,b)]

runNA :: (Alphabet l, Ord s) => NDetAut l s  -> s -> [l] -> [([l], s)]
runNA na st input = 
  case input of
    [] -> ([],) <$> epReachable (ndelta na) st
    (w:ws) -> concatMap (\s -> runNA na s input) nsucc ++
              case wsucc of
                [] -> [(input,st)]
                ls -> concatMap (\s -> runNA na s ws) ls
      where wsucc = ndelta na (Just w) st
    where   nsucc = ndelta na Nothing  st

ndautAccept :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> Bool
ndautAccept na s0 w = any (\(ls,st) -> null ls && st `elem` naccept na) $
                      runNA na s0 w

ndfinalStates :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> [s]
ndfinalStates na s0 w = snd <$> runNA na s0 w

-- trivial forgetful DA -> NA
fromDA :: (Alphabet l) => DetAut l s -> NDetAut l s
fromDA da = NA { nstates = states da
               , naccept = accept da
               , ndelta = newDelta } where
  newDelta Nothing _ = []
  newDelta (Just l) st = [delta da l st]

-- The Power-set Construction: NA -> DA 
fromNA :: (Alphabet l, Ord s) => NDetAut l s -> DetAut l (Set.Set s)
fromNA nda = DA { states = Set.toList dasts
                , accept = Set.toList $ Set.filter acchelp dasts
                , delta = fromTransNA ntrans
                }
  where ndasts = nstates nda
        dasts  = Set.powerSet $ Set.fromList ndasts
        ndaacc = naccept nda
        acchelp set = not $ Set.disjoint set $ Set.fromList ndaacc
        ntrans = ndelta nda

epReachable :: (Alphabet l, Ord s) => (Maybe l -> s -> [s]) -> s -> [s]
epReachable ntrans st = st : concatMap (epReachable ntrans) 
                                       (ntrans Nothing st)

fromTransNA :: (Alphabet l, Ord s) => (Maybe l -> s -> [s]) -> 
                                      l -> Set.Set s -> Set.Set s
fromTransNA ntrans sym set = result
  where starts = listUnions (epReachable ntrans) set
        step = listUnions (ntrans $ Just sym) starts
        result = listUnions (epReachable ntrans) step
        listUnions f input = Set.unions $ Set.map Set.fromList $ Set.map f input
-- listUnions :: (Ord s) => (s -> [s]) -> Set.Set s -> Set.Set s

fromStartNA :: (Alphabet l, Ord s) => NDetAut l s -> s -> Set.Set s
fromStartNA nda st = Set.fromList $ epReachable ntrans st
  where ntrans = ndelta nda

-- test cases

updateNA :: (NDetAut Letter Int,Int) -> (NDetAut Letter Int,Int)
updateNA (nda, s) = (newNDA, s0)
  where (newdata, s0) = regToAut $ autToReg (decode nda,s)
        newNDA = fromJust $ encodeNA newdata

myAutData :: AutData Letter Int
myAutData = AD [1,2,3,4]        -- the states
               [4]              -- accepting states
               [(1,[(Just A,1)  -- the transitions
                   ,(Just B,2)
                   ,(Just C,3)])
               ,(2,[(Just A,4)
                   ,(Just B,2)
                   ,(Just C,1)])
               ,(3,[(Just A,1)
                   ,(Just B,4)
                   ,(Just C,3)])
               ,(4,[(Just A,4)
                   ,(Just B,4)
                   ,(Just C,4)])]

myDACheck :: Bool
myDACheck = detCheck myAutData

myDA :: DetAut Letter Int
myDA = fromJust $ encodeDA myAutData

-- an accepting sequence of inputs
myInputs :: [Letter]
myInputs = [A,A,A,A,B,C,B,B,B,A]

myTestRun :: (Int, Bool)
myTestRun = (finalst, result)
  where finalst = run myDA 1 myInputs
        result = acceptDA myDA 1 myInputs

myNAutData :: AutData Letter Int
myNAutData = AD [1,2,3,4]         -- the states
                [4]               -- accepting states
                [(1,[(Nothing,2)
                    ,(Just C,3)])
                ,(2,[(Nothing,4)
                    ,(Just B,2)
                    ,(Just C,1)])
                ,(3,[(Just A,1)
                    ,(Just C,3)])
                ,(4,[(Just B,4)
                    ,(Just C,4)])]

myNDA :: NDetAut Letter Int
myNDA = fromJust $ encodeNA myNAutData

myNInputsFalse :: [Letter]
myNInputsFalse = [B,B,A]

myNInputsTrue :: [Letter]
myNInputsTrue = []

myNTestRunFalse :: ([([Letter],Int)],Bool)
myNTestRunFalse = (filist,result)
  where filist = runNA myNDA 1 myNInputsFalse
        result = ndautAccept myNDA 1 myNInputsFalse

myNTestRunTrue :: ([([Letter],Int)],Bool)
myNTestRunTrue = (filist,result)
  where filist = runNA myNDA 1 myNInputsTrue
        result = ndautAccept myNDA 1 myNInputsTrue

-- -----------------
-- REGEX definitions 
-- -----------------

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
  show (Alt r r') = show r ++ "+" ++ show r'
  show (Seq (Alt r r') r'') = "(" ++ show r ++ "+" ++ show r' ++ ")" ++ show r''
  show (Seq r'' (Alt r r')) = show r'' ++ "(" ++ show r ++ "+" ++ show r' ++ ")"
  show (Seq r r') = show r ++ show r'
  show (Star r) = "(" ++ show r ++ ")*"

seqList :: [Regex l] -> Regex l
seqList [l] = l
seqList (l:ls) = Seq l $ seqList ls
seqList [] = Epsilon

altList :: [Regex l] -> Regex l
altList [l] = l
altList (l:ls) = Alt l $ altList ls
altList [] = Empty

seqList', altList' :: [l] -> Regex l
seqList' = seqList . map L
altList' = altList . map L

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
                    (Star (Alt Empty r)) -> simplifyRegex $ Star r
                    (Star (Alt r Empty)) -> simplifyRegex $ Star r
                    (Star (Seq Epsilon r)) -> simplifyRegex $ Star r
                    (Star (Seq r Epsilon)) -> simplifyRegex $ Star r
                    x -> x

regexAccept :: Eq l => Regex l -> [l] -> Bool
-- the empty language accepts no words
regexAccept Empty _    = False
-- if down to the empty string, only accept the empty word
regexAccept Epsilon [] = True  
regexAccept Epsilon _  = False
-- if down to a single letter, only accept that letter (and if longer, reject too)
regexAccept (L _) []   = False
regexAccept (L l) [c] | l == c = True
                      | otherwise = False
regexAccept (L _) (_:_) = False
-- optimisations for simple sequences (one part is just a letter)
regexAccept (Seq (L _) _) [] = False
regexAccept (Seq _ (L _)) [] = False
regexAccept (Seq (L l) r) (c:cs) | l == c = regexAccept r cs
                                 | otherwise = False
regexAccept (Seq r (L l)) cs | last cs == l = regexAccept r (init cs)
                             | otherwise = False
-- general Seq case is less efficient
regexAccept (Seq r r') cs = any (regexAccept r' . snd) (initCheck r cs) 
-- general Alt case pretty easy
regexAccept (Alt r r') cs = regexAccept r cs || regexAccept r' cs
-- if word is empty, star is true
regexAccept (Star _) [] = True
-- general star case
regexAccept (Star r) cs = any (regexAccept (Star r) . snd) (initCheck r cs)

-- get all initial sequences of the word that match the regex
initCheck :: Eq l => Regex l -> [l] -> [([l],[l])]
initCheck r w = filter (regexAccept r . fst) (splits w)

-- utility functions

-- splits a list into all possible (order preserving) divisions of it
-- e.g. [1,2,3] becomes [([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]
splits :: [a] -> [([a],[a])]
splits [] = [([],[])]
splits (x:xs) = map (appendFst x) (splits xs) ++ [([],x:xs)]

-- append to the front of the first of a pair of lists
appendFst :: a -> ([a],[a]) -> ([a],[a])
appendFst x (y,z) = (x:y,z)
        
-- ---------------
-- REGEX to DetAut
-- ---------------

-- Since regex to automata inducts on the transition functions, we need a way to glue or reshape our automata nicely
-- As we add more states we need to relable them. The base states are 1 and 2, multiplying by 3 is sequence, multiplying by 5 and 7 is Alt, multiplying by 11 is Star

--useful function to glue states together
transForState :: Eq s => AutData l s -> s -> [(Maybe l, s)]
transForState aut s 
  | isNothing $ lookup s $ transitionData aut = []
  | otherwise = fromJust $ lookup s $ transitionData aut

-- For each operator we define two corresponding functions. One outputs the automata data associated with that operator, 
-- the other stitches and modifies the transition function across the inputs automata (mostly using Epsilon transitions)

regToAut :: Regex l -> (AutData l Int, Int) 
-- gives an integer automata and a starting state
regToAut (L l) = (AD [1,2] [2] [(1, [(Just l,2)]), (1, [(Just l,2)])], 1) 
regToAut Empty = (AD [1,2] [2] [], 1)
regToAut Epsilon = (AD [1,2] [2] [(1, [(Nothing, 2)])], 1)
regToAut (Seq a b) = seqRegAut  (regToAut a) (regToAut b)
regToAut (Alt a b) = altRegAut  (regToAut a) (regToAut b)
regToAut (Star a) = starRegAut $ regToAut a

seqRegAut :: (AutData l Int, Int) -> 
             (AutData l Int, Int) -> 
             (AutData l Int, Int)
seqRegAut (aut1,s1) (aut2,s2) = (AD 
  (stateData aut1 ++ [x*3 | x <- stateData aut2])
  [3*x | x <- acceptData aut2] 
  (gluingSeq (aut1, s1) (aut2, s2))
  , s2)

gluingSeq :: (AutData l Int, Int) -> (AutData l Int, Int) -> 
             [(Int, [(Maybe l, Int)])]
gluingSeq (aut1, _) (aut2, s2) =  firstAut ++ middle ++ secondAut where
  firstAut = [(x, transForState aut1 x) | x<- stateData aut1, x `notElem` acceptData aut1]
  middle = [(x, transForState aut1 x ++ [(Nothing, 3*s2)]) | x<- acceptData aut1]
  secondAut = [(x*3, multTuple 3 (transForState aut2 x)) | x<- stateData aut2]

altRegAut :: (AutData l Int, Int) -> (AutData l Int, Int) -> (AutData l Int, Int)
altRegAut (aut1, s1) (aut2, s2) = (AD 
  ([1,2]++[x*5| x<- stateData aut1]++[x*7| x<- stateData aut2])
  [2] 
  (gluingAlt (aut1, s1) (aut2, s2))
  ,1)

gluingAlt :: (AutData l Int, Int)->(AutData l Int, Int) -> 
             [(Int, [(Maybe l, Int)])]
gluingAlt (aut1,s1) (aut2,s2) = start ++ firstAut ++endFirstAut ++ secondAut ++ endSecondAut where
  start = [(1, [(Nothing, s1*5)]), (1, [(Nothing, s2*7)])]
  firstAut = [(x*5, multTuple 5 (transForState aut1 x) ) | x<- stateData aut1, x `notElem` acceptData aut1]
  secondAut = [(x*7, multTuple 7 (transForState aut2 x) ) | x<- stateData aut2, x `notElem` acceptData aut2]
  endFirstAut = [(x*5, multTuple 5 (transForState aut1 x) ++ [(Nothing,2)] ) | x<- acceptData aut1]
  endSecondAut = [(x*7, multTuple 7 (transForState aut2 x) ++ [(Nothing,2)] ) | x<- acceptData aut2]

starRegAut :: (AutData l Int, Int) -> (AutData l Int,Int)
starRegAut (aut, s) = (AD (1:[x*11 | x<- stateData aut])
                    [1]
                    (gluingStar (aut, s))
                    ,1)

gluingStar :: (AutData l Int, Int)-> [(Int, [(Maybe l, Int)])]
gluingStar (aut1, s1) = start ++ middle ++ end where
  start = [(1, [(Nothing, s1*11)])]
  middle = [(x, multTuple 11 (transForState aut1 x))| x<-stateData aut1, x `notElem` acceptData aut1]
  end = [(a, (Nothing, 1) : multTuple 11 (transForState aut1 a)) | a <- acceptData aut1]

multTuple :: Int -> [(a,Int)] -> [(a,Int)]
multTuple _ [] = []
multTuple n ((a,b):xs) = (a,n*b) : multTuple n xs

-- -----------------------------
-- Automaton to Regex Conversion
-- -----------------------------

-- Take a collection of data and starting states, outputs a regular expression which corresponds to the language.
autToReg :: Eq l => Ord s => (AutData l s, s)-> Regex l
autToReg (aut, s)= kleeneAlgo intAut 0 lastState lastState where 
 intAut = (fst.cleanAutomata.relableAut) (aut,s)
 lastState = length (stateData intAut) - 1 
--autToReg aut [s]= kleeneAlgo newAut 0 (length stateData aut) (length stateData aut) where newAut = cleanAutomata . relableAut aut

--following the Wikipedia page, this function recursively removes elements and uses the removed transition lables to construct the regex. 
kleeneAlgo:: Eq l => AutData l Int -> Int -> Int -> Int -> Regex l
kleeneAlgo aut i j (-1) = simplifyRegex (if i==j 
                                         then Alt Epsilon (altSet [ maybe Epsilon L a | a <- successorSet aut i j]) 
                                         else altSet [ maybe Epsilon L a | a <- successorSet aut i j])
kleeneAlgo aut i j k = Alt (simplifyRegex(kleeneAlgo aut i j (k-1))) 
                           (simplifyRegex (seqSet [ simplifyRegex(kleeneAlgo aut i k (k-1))
                                                  , simplifyRegex (Star (kleeneAlgo aut k k (k-1)))
                                                  , simplifyRegex (kleeneAlgo aut k j (k-1)) ]))

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
                           [(relableHelp aut s, [ (a, relableHelp aut b)| (a,b) <- transForState aut s] ) | s<- stateData aut]
                       , relableHelp aut s1)

-- take aut data and make a nice start state/end state
cleanAutomata:: (AutData l Int, Int) -> (AutData l Int, Int)
cleanAutomata (aut, s) = (AD (0:lastState:stateData aut)
                          [lastState]
                          (cleanTransition (aut,s))
                         , 0) where lastState = 1 + length (stateData aut)
 
cleanTransition:: (AutData l Int, Int) -> [(Int, [(Maybe l, Int)])]
cleanTransition (aut, s) = start ++ middle ++ end where
  start = [(0, [(Nothing, s)])]
  middle = [(x, transForState aut x) | x <- stateData aut, x `notElem` acceptData aut]
  end = [(x, (Nothing, length (stateData aut) + 1) : transForState aut x) | x<- acceptData aut]

 -- Examples

exampleAut :: AutData String Int
exampleAut = AD [1,2,3] [2] [(1, [(Just "a", 1), (Just "b", 2)]), (2, [(Just "b", 2), (Just "a", 3)   ]), (3, [(Just "a", 2), (Just "b", 2)])]

exampleAut2 :: AutData String Int
exampleAut2 = AD [1,2,3,4] [4] [(1, [(Just "a", 2)]), (2, [(Just "a", 3)]), (3, [(Just "a", 4)])]
\end{code}
