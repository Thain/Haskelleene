
\section{The most basic library}\label{sec:Basics}

In this section we define our most basic data structures: a finite input alphabet

\begin{code}
module Basics where

import Data.List
import Test.QuickCheck

-- a typeclass for finite alphabets
class Ord a => Alphabet a where
  completeList :: [a]

-- alphIter should check if the list contains exactly the elements of the type
-- this function will be used for ensuring an AutData encodes a deterministic automaton
alphIter :: Alphabet a => [a] -> Bool
alphIter l = sort l == completeList 

-- The specific input alphabet we will use. 
data Letter = A | B | C deriving (Eq, Ord)
-- data Letter = A | B | C | D | E deriving (Eq, Ord)

instance Show Letter where
  show A = "a"
  show B = "b"
  show C = "c"
  -- show D = "d"
  -- show E = "e"

instance Alphabet Letter where
  completeList = [A,B,C]

instance Arbitrary Letter where
  arbitrary = elements completeList

type TDict l s = [(s, [(Maybe l, s)])]

-- l is the type of our alphabet (most likely a finite set),
-- s is the type of our states
-- Maybe l because we allow empty transitions
data AutData l s = AD { stateData :: [s] 
                      , acceptData :: [s] 
                      , transitionData :: TDict l s }
                      deriving Show

-- given data in the format of transitionData, an input state, and input
-- letter, output all possible input/output pairs.
getTrs :: (Eq a, Eq b) => [(a,[(b,a)])] -> a -> b -> [(b,a)]
getTrs allTrs s0 ltr = filter (\x -> fst x == ltr) $ filter (\x -> fst x == s0) allTrs >>= snd

-- utility for checking if a list has duplicates
allUnq:: Eq a => [a] -> Bool
allUnq = unqHelp []
    where
        unqHelp _ [] = True
        unqHelp seen (x:xs) = elem x seen && unqHelp (x:seen) xs


-- splits a list into all possible (order preserving) divisions of it
-- e.g. [1,2,3] becomes [([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]
splits :: [a] -> [([a],[a])]
splits [] = [([],[])]
splits (x:xs) = map (appendFst x) (splits xs) ++ [([],x:xs)]

-- append to the front of the first of a pair of lists
appendFst :: a -> ([a],[b]) -> ([a],[b])
appendFst x (y,z) = (x:y,z)

appendTuple :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
appendTuple (l,l') (m,m') = (l++m,l'++m')

\end{code}
