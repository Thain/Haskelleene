\section{The most basic library}\label{sec:Basics}

This section describes a module which we will import later on.

\begin{code}
module Basics where

import Control.Monad.State
import qualified Control.Category as Cat

type AState  = Int -- maybe wrap in constructor
type Output = Bool -- maybe wrap in constructor
type Letter = Int  -- maybe wrap in constructor

type DTrans = State AState Output -- StateT with Identity monad
type NTrans = StateT AState [] Output 

-- easy composition of deterministic transitions
-- LY: this is the same as (>>)
-- (<.>) :: DTrans -> DTrans -> DTrans
-- (<.>) a b = a >>= const b -- ignore the output of the intermediate state

-- want to make the above work with this typeclass
-- LY: Category in haskell is defined to accept a kind (* -> * -> *), while DTrans has kind *
-- instance Category DTrans where
--  id = StateT $ \s -> (val s, s)
--  (.) = (>>)

-- easy shorthand for defining transitions
-- LY: Please change this name to something else. Better: This really sounds like (<$>).
l :: (AState -> AState) -> DTrans
l f = StateT $ \s -> return (val (f s), (f s))

-- good for testing
showRun :: AState -> DTrans -> String
showRun s t = show $ runState t s

type Valuation = AState -> Output -- could also do set of AState

-- for the moment our state set is N, and all states > 10 are accepting

val :: Valuation
val x = x > 10

-- make a plus transition
plus :: Int -> DTrans
plus = \x -> l (+x)
-- pTrans = l $ (+)

-- make a subtraction transition
-- LY: VERY VERY VERY BAD name for this, this shadows ALL the s appearing in this file! Haskell does not evaluate from top to bottom! I also change the previous short names...
-- s :: Int -> DTrans
-- s = \x -> l (subtract x)
subt :: Int -> DTrans
subt = \x -> l (subtract x)

-- big list of transitions
tlist = [(subt 3), (plus 2), (plus 3), (subt 10), (plus 19)]

-- here's how we can compose em all together
composed = foldr (>>) (l id) tlist

test :: String
test = showRun 9 composed
-- initial state is 9

data DetAut = DA { states :: [AState]
                 , delta :: Letter -> DTrans }

type AutData = ( [AState]                    -- all states
               , [AState]                    -- accepting states
               , [(AState, Letter, AState)]) -- transitions

-- can it define a deterministic automaton? (totality of transition)
safetyCheck :: AutData -> Bool
safetyCheck = undefined

-- contingent on passing safetyCheck, make it into a DA
encodeDA :: AutData -> Maybe DetAut
encodeDA d | safetyCheck d = Just undefined
           | otherwise = Nothing

-- make it into an NA
-- encodeNA :: AutData -> NDetAut
-- encodeNA = undefined

newtype NDetState s a = NST { run :: s -> [(a, s)] }

-- s -> [(a,s)]
-- NTrans b = ST $ s -> 

-- 
-- ~> for transitioning states?
\end{code}
