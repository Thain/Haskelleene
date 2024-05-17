\section{The most basic library}\label{sec:Basics}

This section describes a module which we will import later on.

\begin{code}
module Basics where

import Control.Monad.State
import Data.Maybe
import Data.List

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
               stTrans ltr st = return (calcV ltr st, calcS ltr st)
               calcV ltr st = calcS ltr st `elem` acceptData d
               calcS ltr st = fromJust $ lookup (Just ltr) $ fromJust (lookup st (transitionData d)) 

nothingTransition :: (Eq s) => DetAut l s -> State s Bool
nothingTransition da = StateT $ \s -> return (elem s (accept da), s)

-- takes DA, input letter list, and initial state to output pair
run :: (Eq s) => DetAut l s -> [l] -> s -> (Bool, s)
run da w s0 = (`runState` s0) $ foldl' (>>) (nothingTransition da) (map (delta da) w) 

autAccept :: (Eq s) => DetAut l s -> [l] -> s -> Bool
autAccept da w s0 = fst $ run da w s0

finalState :: (Eq s) => DetAut l s -> [l] -> s -> s
finalState da w s0 = snd $ run da w s0

-- NA definitions

-- "StateT s [] Bool" is "s -> [(Bool,s)]"
data NDetAut l s = NA { nstates :: [s]
                      , naccept :: [s]
                      , ndelta :: Maybe l -> StateT s [] Bool }


-- make data into an NA (no need for safety check)
encodeNA :: (Alphabet l, Eq l, Eq s) => AutData l s -> NDetAut l s
encodeNA d = NA { nstates = stateData d
                , naccept = acceptData d
                , ndelta = StateT . stTrans } where
  stTrans st ltr = zip (vals st ltr) (outSts st ltr)
  vals st ltr = map (`elem` (acceptData d)) $ outSts st ltr
  outSts st ltr = map snd $ getTrs (transitionData d) ltr st

runNA :: NDetAut l s -> [l] -> s -> [(Bool, s)]
runNA = undefined
-- runNA na w s0 = (`runState` s0) $ foldl' (>>) (pure False) (map (delta na) w) 

ndautAccept :: NDetAut l s -> [l] -> s -> Bool
ndautAccept = undefined
-- ndautAccept na w s0 = any $ runNA na w s0

ndfinalStates :: NDetAut l s -> [l] -> s -> [s]
ndfinalStates = undefined
-- ndfinalStates na w s0 = snd $ runNA na w s0

-- REGEX definitions 

data Regex l = Empty | Epsilon | L l | Alt (Regex l) (Regex l) | Seq (Regex l) (Regex l) | Star (Regex l) 

instance Eq l => Eq (Regex l) where
  (==) Empty Empty = True
  (==) Epsilon Epsilon = True
  (==) (L l) (L l') = l == l'
  (==) (Alt r r') (Alt r'' r''') = compsEq r r' r'' r'''
  (==) (Seq r r') (Seq r'' r''') = (r == r'') && (r' == r''')
  (==) (Star r) (Star r') = r == r'
  (==) _ _ = False
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
                    (Star (Star r)) -> simplifyRegex r
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

