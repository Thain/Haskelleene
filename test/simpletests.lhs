\section{Simple Tests}\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Basics

import Test.Hspec
import Test.QuickCheck
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

Here is the example deterministic automaton that is below:
\[\begin{tikzcd}
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
\end{tikzcd}\]

\begin{code}
main :: IO ()
main = hspec $ do
  describe "Basics" $ do
    it "somenumbers should be the same as [1..10]" $
      somenumbers `shouldBe` [1..10]
    it "if n > - then funnyfunction n > 0" $
      property (\n -> n > 0 ==> funnyfunction n > 0)
    it "myreverse: using it twice gives back the same list" $
      property $ \str -> myreverse (myreverse str) == (str::String)

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

myTestRun :: (Bool, Int)
myTestRun = run myDA myInputs 1

myNAData :: AutData Letter Int
myNAData = AD [1,2,3]
              [3]
              [(1,[(Nothing,2)])
              ,(2,[])
              ,(3,[])]

                    
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
