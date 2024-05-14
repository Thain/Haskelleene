\section{The most basic library}\label{sec:Basics}

This section describes a module which we will import later on.

\begin{code}
module Basics where

import Control.Monad.State
import Data.Maybe
import Data.Functor.Identity
import Data.List
-- import Data.List.Extra

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
-- "StateT s [] Bool" is "s -> [(Bool,s)]"

data DetAut  l s = DA { states :: [s]
                      , delta :: l -> State s Bool }

data NDetAut l s = NA { nstates :: [s]
                      , ndelta :: Maybe l -> StateT s [] Bool }

-- just a b c for now
data Letter = A | B | C deriving (Eq, Ord)
-- data Letter = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

alphSize :: Int
alphSize = 3

-- can the data define a det automaton? (totality of transition)
detCheck :: (Eq l, Eq s) => AutData l s -> Bool
detCheck ad = length sts == length (stateData ad) && allUnq sts  -- all states are in transitionData exactly once
              && all detCheckHelper stateTrs where               -- check transitions for each letter exactly once
  sts = map fst $ transitionData ad
  stateTrs = map snd $ transitionData ad

detCheckHelper :: (Eq l, Eq s) => [(Maybe l,s)] -> Bool
detCheckHelper trs = notElem Nothing inputs      -- no empty transitions
                     && length inputs == alphSize   -- correct number of transitions
                     && allUnq inputs where         -- all state/letter pairs unique
  inputs = map fst trs

-- contingent on passing safetyCheck, make data into a DA
encodeDA :: (Eq l, Eq s) => AutData l s -> Maybe (DetAut l s)
encodeDA d | not $ detCheck d = Nothing
           | otherwise = Just $ DA { states = stateData d
                                   , delta = StateT . stTrans } where
               stTrans l s = return (calcV l s, calcS l s)
               calcV l s = calcS l s `elem` acceptData d
               calcS l s = fromJust $ lookup (Just l) $ fromJust (lookup s (transitionData d)) 
               
-- make data into an NA (no need for safety check)
encodeNA :: AutData l s -> NDetAut l s
encodeNA d = NA { nstates = stateData d
                , ndelta = undefined }

-- todo:
-- - make a list of transitions easily
-- - compose them using (>>) and foldr

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

-- myTrs :: [State Int Bool]
-- myTrs = map (delta myDA) myInputs 

-- foldl so we don't lose the last output! could we do without a base case? by hand?
composed :: State Int Bool
composed = foldl (>>) (StateT (\s -> return (False,s))) (map (delta myDA) myInputs)

output :: (Bool,Int)
output = runState composed 1

-- takes DA, input letter list, and initial state to output pair
run :: DetAut l s -> [l] -> s -> (Bool, s)
run = undefined

accept :: DetAut l s -> [l] -> s -> Bool
accept aut word initstate = fst $ run aut word initstate

finalState :: DetAut l s -> [l] -> s -> s
finalState aut word initstate = snd $ run aut word initstate

\end{code}
