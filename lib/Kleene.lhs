
\section{Deterministic Automata Library}\label{sec:DetAut}

This is where we define the deterministic automaton data structure we will be using throughout the project.

\begin{code}
module Kleene where

import Basics      -- contains all of our utility functions
import Automata    -- contains automaton definitions/conversions
import Regex       -- contains regex definitions
import Data.Maybe

import qualified Data.Map.Strict as Map

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

fromReg :: (Alphabet l) => Regex l -> (NDetAut l Int, Int)
fromReg reg = (fromJust (encodeNA ndata),st)
  where (ndata,st) = regToAut reg

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
 intAut = (fst.cleanAutomata.relabelAut) (aut,s)
 lastState = length (stateData intAut) - 1 
--autToReg aut [s]= kleeneAlgo newAut 0 (length stateData aut) (length stateData aut) where newAut = cleanAutomata . relabelAut aut

--following the Wikipedia page, this function recursively removes elements and uses the removed transition lables to construct the regex. 
kleeneAlgo:: Eq l => AutData l Int -> Int -> Int -> Int -> Regex l
kleeneAlgo aut i j (-1) = simplifyRegex (if i==j 
                                         then Alt Epsilon (altList [ maybe Epsilon L a | a <- successorSet aut i j]) 
                                         else altList [ maybe Epsilon L a | a <- successorSet aut i j])
kleeneAlgo aut i j k = Alt (simplifyRegex(kleeneAlgo aut i j (k-1))) 
                           (simplifyRegex (seqList [ simplifyRegex(kleeneAlgo aut i k (k-1))
                                                  , simplifyRegex (Star (kleeneAlgo aut k k (k-1)))
                                                  , simplifyRegex (kleeneAlgo aut k j (k-1)) ]))

-- takes some automata data and two states, s1, s2. Ouputs all the ways to get s2 from s1
successorSet :: Eq s => AutData l s -> s -> s -> [Maybe l]
successorSet aut s1 s2 
 | isNothing (lookup s1 (transitionData aut) ) = [] -- if there are no successors
 | otherwise = map fst (filter (\w -> s2 == snd w) (fromJust $ lookup s1 (transitionData aut)) )

-- states as integer makes everything easier. We use a dictionary to relabel in one sweep per say
relabelHelp :: Ord s => AutData l s -> s -> Int
relabelHelp aut s = fromJust (Map.lookup s (Map.fromList $ zip (stateData aut) [1 .. (length (stateData aut)+1)]))

relabelAut :: Ord s => (AutData l s, s) -> (AutData l Int, Int)
relabelAut (aut, s1) = (AD [relabelHelp aut s | s <- stateData aut]
                           [relabelHelp aut s| s<- acceptData aut]
                           [(relabelHelp aut s, [ (a, relabelHelp aut b)| (a,b) <- transForState aut s] ) | s<- stateData aut]
                       , relabelHelp aut s1)

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

\end{code}
