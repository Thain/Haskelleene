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

decodeNA :: (Alphabet l, Eq s) => NDetAut l s -> AutData l s
decodeNA nda = AD { stateData = sts
                  , acceptData = naccept nda
                  , transitionData = trandata
                  }
  where sts = nstates nda
        ntrans = ndelta nda
        symlist = Nothing : (Just <$> completeList)
        trandata = graph help sts
          where help st = concatMap (\sym -> (sym,) <$> ntrans sym st) symlist

graph :: (a -> b) -> [a] -> [(a,b)]
graph f as = zip as $ f <$> as

runNA :: NDetAut l s  -> s -> [l] -> [([l], s)]
runNA na st input = 
  case input of
    [] -> ([],st) : concatMap (\s -> runNA na s input) nsucc
    (w:ws) -> case wsucc of
                [] -> (input,st) : concatMap (\s -> runNA na s input) nsucc
                ls -> concatMap (\s -> runNA na s ws) ls ++ 
                      concatMap (\s -> runNA na s input) nsucc
      where wsucc = ndelta na (Just w) st
    where   nsucc = ndelta na Nothing  st

ndautAccept :: (Alphabet l, Eq s) => NDetAut l s -> s -> [l] -> Bool
ndautAccept na s0 w = any (\(ls,st) -> null ls && st `elem` naccept na) $
                      runNA na s0 w

ndfinalStates :: NDetAut l s -> s -> [l] -> [s]
ndfinalStates na s0 w = snd <$> runNA na s0 w

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
        result = listUnions (ntrans $ Just sym) starts
        listUnions f input = Set.unions $ Set.map Set.fromList $ Set.map f input
-- listUnions :: (Ord s) => (s -> [s]) -> Set.Set s -> Set.Set s

fromStartNA :: (Alphabet l, Ord s) => NDetAut l s -> s -> Set.Set s
fromStartNA nda st = Set.fromList $ epReachable ntrans st
  where ntrans = ndelta nda

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
seqList' = seqList . (map L)
altList' = altList . (map L)

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
