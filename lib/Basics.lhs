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

alphSize :: Int
alphSize = 3

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
                    
exampleRegex :: Regex Letter
exampleRegex = Star (Alt (L A) (L B))

annoyingRegex :: Regex Letter
annoyingRegex = Alt Empty (Seq Epsilon (L A))

strToRegex :: String -> (Regex Letter)
strToRegex = undefined

\end{code}
