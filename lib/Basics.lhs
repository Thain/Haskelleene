{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE InstanceSigs #-}
\section{The most basic library}\label{sec:Basics}

This section describes a module which we will import later on.

\begin{code}
module Basics where

-- import Control.Monad.State
import Data.Maybe
import Data.List
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

instance Arbitrary Letter where
  arbitrary = elements [A,B,C]

instance Show Letter where
  show A = "a"
  show B = "b"
  show C = "c"

instance Alphabet Letter where
  completeList = [A,B,C]
  -- data Letter = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

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

-- NA -> DA transition

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

listUnions :: (Ord s) => (s -> [s]) -> Set.Set s -> Set.Set s
listUnions f input = Set.unions $ Set.map Set.fromList $ Set.map f input

fromTransNA :: (Alphabet l, Ord s) => (Maybe l -> s -> [s]) -> 
                                      l -> Set.Set s -> Set.Set s
fromTransNA ntrans sym set = result
  where starts = listUnions (epReachable ntrans) set
        result = listUnions (ntrans $ Just sym) starts

fromStartNA :: (Alphabet l, Ord s) => NDetAut l s -> s -> Set.Set s
fromStartNA nda st = Set.fromList $ epReachable ntrans st
  where ntrans = ndelta nda

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
  show (Alt r r') = "(" ++ show r ++ "|" ++ show r' ++ ")"
  show (Seq r r') = show r ++ show r'
  show (Star r) = "(" ++ show r ++ ")*"

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
                    x -> x

-- REGEX to DetAut
-- Since regex to automata inducts on the transition functions, we need a way to glue or reshape our automata nicely
regToAut :: Regex l -> AutData l Int
regToAut = undefined
-- regToAut (L l) = AD [1,2] [2] [(1, [(Just l,2)]), (1, [(Just l,2)])] 
-- regToAut (Seq (L l) (L l')) = seqRegAut $ (regToAut (L l)) (regToAut (L l')) 

seqRegAut :: AutData l Int -> AutData l Int -> AutData l Int
seqRegAut = undefined
-- seqRegAut aut1 aut2 = AD [x | x <- stateData aut2 ]++[x*10 | x <- stateData aut2] [x | x <- acceptData] [(x*10, gluingStatesSeq x aut1 aut2 ) | x <- stateData aut1]

gluingStatesSeq :: Int -> AutData l Int -> AutData l Int -> AutData l Int
gluingStatesSeq = undefined
-- gluingStatesSeq  x aut1 aut2 = undefined
 -- | x `elem` acceptData aut1 = fromJust  (lookup x transitionData aut1)++(Epsilon, StartingState)
 -- |otherwise  fromJust  (lookup x transitionData aut1)

\end{code}

