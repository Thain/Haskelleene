import Control.Monad.State
import qualified Control.Category

type AState  = Int -- maybe wrap in constructor
type Output = Bool -- maybe wrap in constructor
type Letter = Int  -- maybe wrap in constructor

type DTrans = State AState Output -- StateT with Identity monad
type NTrans = StateT AState [] Output 

-- easy composition of deterministic transitions
(<.>) :: DTrans -> DTrans -> DTrans
(<.>) a b = a >>= const b -- ignore the output of the intermediate state

-- want to make the above work with this typeclass
-- instance Category DTrans where
    -- id = StateT $ \s -> (val s, s)
    -- (.) a b = a >>= const b

-- easy shorthand for defining transitions
l :: (AState -> AState) -> DTrans
l f = StateT $ \s -> let s' = f s in return (val $ s', s')

-- good for testing
showRun :: AState -> DTrans -> String
showRun s t = show $ runState t s

type Valuation = AState -> Output -- could also do set of AState

-- for the moment our state set is N, and all states > 10 are accepting

val :: Valuation
val x = x > 10

-- make a plus transition
p :: Int -> DTrans
p = \x -> l (+x)
-- pTrans = l $ (+)

-- make a subtraction transition
s :: Int -> DTrans
s = \x -> l (subtract x)

-- big list of transitions
tlist = [(s 3), (p 2), (p 3), (s 10), (p 19)]

-- here's how we can compose em all together
composed = foldr (<.>) (l id) tlist

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
