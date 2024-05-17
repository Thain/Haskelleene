{-# LANGUAGE InstanceSigs #-}
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

-- can the data define a det automaton? (totality of transition)
detCheck :: (Alphabet l, Eq s) => AutData l s -> Bool
detCheck ad = length sts == length (stateData ad) && allUnq sts  -- all states are in transitionData exactly once
              && all detCheckHelper stateTrs where               -- check transitions for each letter exactly once
  sts = fst <$> transitionData ad
  stateTrs = snd <$> transitionData ad

detCheckHelper :: (Alphabet l, Eq s) => [(Maybe l,s)] -> Bool
detCheckHelper trs = notElem Nothing (fst <$> trs)        -- no empty transitions
                     && alphIter (fromJust . fst <$> trs) -- transition set is exactly the alphabet

-- contingent on passing safetyCheck, make data into a DA
encodeDA :: (Alphabet l, Eq s) => AutData l s -> Maybe (DetAut l s)
encodeDA d | not $ detCheck d = Nothing
           | otherwise = Just $ DA { states = stateData d
                                   , accept = acceptData d
                                   , delta = StateT . stTrans } where
               stTrans l s = return (calcV l s, calcS l s)
               calcV l s = calcS l s `elem` acceptData d
               calcS l s = fromJust $ lookup (Just l) $ fromJust (lookup s (transitionData d)) 

-- takes DA, input letter list, and initial state to output pair
run :: DetAut l s -> [l] -> s -> (Bool, s)
run da w s0 = (`runState` s0) $ foldl' (>>) (pure False) (delta da <$> w) 

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
encodeNA :: (Alphabet l, Eq s) => AutData l s -> NDetAut l s
encodeNA d = NA { nstates = stateData d
                , naccept = acceptData d
                , ndelta = StateT . stTrans } where
  stTrans st ltr = zip (vals st ltr) (outSts st ltr)
  vals st ltr = (`elem` acceptData d) <$> outSts st ltr
  outSts st ltr = undefined
  -- getTrs is undefined
  -- snd <$> getTrs (transitionData d) ltr st

runNA :: NDetAut l s -> [l] -> s -> [(Bool, s)]
runNA na w s0 = undefined

ndautAccept :: NDetAut l s -> [l] -> s -> Bool
ndautAccept na w s0 = any fst $ runNA na w s0

ndfinalStates :: NDetAut l s -> [l] -> s -> [s]
ndfinalStates na w s0 = snd <$> runNA na w s0

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
regToAut (L l) = AD [1,2] [2] [(1, [(Just l,2)]), (1, [(Just l,2)])] 
regToAut r = undefined
-- regToAut (Seq (L l) (L l')) = seqRegAut $ (regToAut (L l)) (regToAut (L l')) 

seqRegAut :: AutData l Int -> AutData l Int -> AutData l Int
seqRegAut = undefined
-- seqRegAut aut1 aut2 = AD [x | x <- stateData aut2 ]++[x*10 | x <- stateData aut2] [x | x <- acceptData] [(x*10, gluingStatesSeq x aut1 aut2 ) | x <- stateData aut1]

gluingStatesSeq :: Int -> AutData l Int -> AutData l Int -> AutData l Int
gluingStatesSeq  x aut1 aut2 = undefined
 -- | x `elem` acceptData aut1 = fromJust  (lookup x transitionData aut1)++(Epsilon, StartingState)
 -- |otherwise  fromJust  (lookup x transitionData aut1)

\end{code}

