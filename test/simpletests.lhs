\section{Simple Tests}\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Data.Maybe
import Test.Hspec
-- import Test.QuickCheck
import Basics
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

Here is the example deterministic automaton that is below:
\[
  \begin{tikzcd}
    1 & 2 \\
    3 & 4
    \arrow["a", from=1-1, to=1-1, loop, in=105, out=165, distance=5mm]
    \arrow["b", curve={height=-6pt}, from=1-1, to=1-2]
    \arrow["c"', curve={height=6pt}, from=1-1, to=2-1]
    \arrow["c", curve={height=-6pt}, from=1-2, to=1-1]
    \arrow["b", from=1-2, to=1-2, loop, in=15, out=75, distance=5mm]
    \arrow["a", from=1-2, to=2-2]
    \arrow["a"', curve={height=6pt}, from=2-1, to=1-1]
    \arrow["c", from=2-1, to=2-1, loop, in=195, out=255, distance=5mm]
    \arrow["b"', from=2-1, to=2-2]
    \arrow["{a,b,c}", from=2-2, to=2-2, loop, in=285, out=345, distance=5mm]
  \end{tikzcd}
\]

\begin{code}
main :: IO ()
main = hspec $ do
  describe "Basics" $ do
    it "DA test run result should be (4,True)" $
      myTestRun `shouldBe` (4,True)
    it "NA test run result 1 should be ([([B,B,A],1),([A],2),([A],4),([A],4),([A],4)],False)" $
      myNTestRunFalse `shouldBe` 
      ([([B,B,A],1),([A],2),([A],4),([A],4),([A],4)], False)
    it "NA test run result 2 should be ([([],1),([],2),([],4)], False)" $
      myNTestRunTrue `shouldBe` 
      ([([],1),([],2),([],4)], True)

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
                ,(3,[(Just A,1)
                    ,(Just C,3)])
                ,(4,[(Just B,4)
                    ,(Just C,4)])]

myNDA :: NDetAut Letter Int
myNDA = fromJust $ encodeNA myNAutData

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

exampleRegex :: Regex Letter
exampleRegex = Star (Alt (L A) (L B))

annoyingRegex :: Regex Letter
annoyingRegex = Alt Empty (Seq Epsilon (L A))

\end{code}

To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.

