
\section{Examples}\label{sec:Examples}

\begin{code}

module Examples where

import Basics
import Automata
import Regex
import Kleene
import Data.Maybe

-- ----------------------
-- DETERMINISTIC AUTOMATA
-- ----------------------

-- Automata

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

myTestRun :: (Int, Bool)
myTestRun = (finalst, result)
  where finalst = run myDA 1 myInputs
        result = acceptDA myDA 1 myInputs

myNAutData :: AutData Letter Int
myNAutData = AD [1,2,3,4]         -- the states
                [4]               -- accepting states
                [(1,[(Nothing,2)
                    ,(Just C,3)])
                ,(2,[(Nothing,4)
                    ,(Just B,2)
                    ,(Just C,1)])
                ,(1,[(Just A,2), -- want to merge these with above
                     (Just A,3)])
                ,(3,[(Just A,1)
                    ,(Just C,3)])
                ,(1,[(Nothing,1)  -- want to be ignoring this
                    ,(Nothing,3)  -- want to merge these with above
                    ,(Just A,4)])
                ,(4,[(Just B,4)
                    ,(Just C,4)])]

myNDA :: NDetAut Letter Int
myNDA = encodeNA myNAutData

-- what epsilon transitions does 1 have? should just be to state 2
nothingFrom1 :: [Int]
nothingFrom1 = (ndelta myNDA) Nothing 1

myNInputsFalse :: [Letter]
myNInputsFalse = [B,B,A]

myNInputsTrue :: [Letter]
myNInputsTrue = []

myNTestRunFalse :: ([([Letter],Int)],Bool)
myNTestRunFalse = (filist,result)
  where filist = runNA myNDA 1 myNInputsFalse
        result = ndautAccept myNDA 1 myNInputsFalse

myNTestRunTrue :: ([([Letter],Int)],Bool)
myNTestRunTrue = (filist,result)
  where filist = runNA myNDA 1 myNInputsTrue
        result = ndautAccept myNDA 1 myNInputsTrue

exampleAut :: AutData String Int
exampleAut = AD [1,2,3] [2] [(1, [(Just "a", 1), (Just "b", 2)]), (2, [(Just "b", 2), (Just "a", 3)   ]), (3, [(Just "a", 2), (Just "b", 2)])]

exampleAut2 :: AutData String Int
exampleAut2 = AD [1,2,3,4] [4] [(1, [(Just "a", 2)]), (2, [(Just "a", 3)]), (3, [(Just "a", 4)])]


-- Regexes

exampleRegex :: Regex Letter
exampleRegex = Star (Alt (L A) (L B))

annoyingRegex :: Regex Letter
annoyingRegex = Alt Empty (Seq Epsilon (L A))

-- examples
abc,abca,aOrbc :: Regex Letter
abc = seqList' [A,B,C]
abca = seqList' [A,B,C,A]
aOrbc = Seq abc $ Star (Alt (L A) (Seq (L B) (L C)))


\end{code}
