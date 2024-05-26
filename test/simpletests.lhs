<<<<<<< Updated upstream
\section{Simple Tests}\label{sec:simpletests}
=======

\subsection{Simple Tests}\label{sec:simpletests}
>>>>>>> Stashed changes

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

<<<<<<< Updated upstream
import Basics

import Test.Hspec
import Test.QuickCheck
=======
import Test.Hspec ( hspec, describe, it, shouldBe )
import Test.Hspec.QuickCheck ( prop )
import Test.QuickCheck ( (==>) )
import Automata
    ( ndautAccept, acceptDA, fromNA, fromStartNA, decode )
import Regex ( regexAccept )
import Kleene ( fromReg, dautToReg, autToReg )
import Examples ( myTestRun, myNDA, exampleRegex, wikiDA )
>>>>>>> Stashed changes
\end{code}

% Here is the example deterministic automaton that is below:
% \[
%   \begin{tikzcd}
%     1 & 2 \\
%     3 & 4
%     \arrow["a", from=1-1, to=1-1, loop, in=105, out=165, distance=5mm]
%     \arrow["b", curve={height=-6pt}, from=1-1, to=1-2]
%     \arrow["c"', curve={height=6pt}, from=1-1, to=2-1]
%     \arrow["c", curve={height=-6pt}, from=1-2, to=1-1]
%     \arrow["b", from=1-2, to=1-2, loop, in=15, out=75, distance=5mm]
%     \arrow["a", from=1-2, to=2-2]
%     \arrow["a"', curve={height=6pt}, from=2-1, to=1-1]
%     \arrow["c", from=2-1, to=2-1, loop, in=195, out=255, distance=5mm]
%     \arrow["b"', from=2-1, to=2-2]
%     \arrow["{a,b,c}", from=2-2, to=2-2, loop, in=285, out=345, distance=5mm]
%   \end{tikzcd}
% \]

<<<<<<< Updated upstream
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
=======
We have tested the following basic facts:

\begin{itemize}
\item A basic running example for a deterministic automaton.
\item The behavioural equivalence of determinisitic and non-deterministic automata under the conversion implemented in Section~\ref{sec:Automata}.
\item The behavioural equivalence of regular expressions and its corresponding non-deterministic automaton implemented in Section~\ref{sec:DetAut}.
\item The behavioural equivalence of a deterministic automaton and its corresponding regular expression implemented in Section~\ref{sec:DetAut}.
\item The behavioural equivalence of a non-deterministic automaton and its corresponding regular expression implemented in Section~\ref{sec:DetAut}.
\end{itemize}
>>>>>>> Stashed changes

\begin{code}
main :: IO ()
main = hspec $ do
<<<<<<< Updated upstream
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
=======
  describe "Examples" $ do
    it "DA test run result should be (4,True)" $
      myTestRun `shouldBe` (4,True)
    prop "NA and transfer to DA should give the same result" $
      \input -> ndautAccept myNDA 1 input == acceptDA (fromNA myNDA) (fromStartNA myNDA 1) input
    prop "reg to NA should give the same result" $
      \input -> regexAccept exampleRegex input == uncurry ndautAccept (fromReg exampleRegex) input
    prop "DA to reg should give the same result" $
      \input -> length input <= 30 ==> 
                acceptDA wikiDA 0 input == regexAccept (dautToReg wikiDA 0) input
    prop "NA to reg should give the same result" $
      \input -> length input <= 30 ==> 
                ndautAccept myNDA 1 input == regexAccept (autToReg (decode myNDA, 1)) input
\end{code}

The result is recorded below. The reason in the last two cases we restrict the arbitrarily generated input data to have length less than 30 is that the current algorithms is not efficient enough to run the semantics for larger inputs on regular expressions.

\begin{showCode}
Examples
  DA test run result should be (4,True) [\/]
  NA and transfer to DA should give the same result [\/]
    +++ OK, passed 100 tests.
  reg to NA should give the same result [\/]
    +++ OK, passed 100 tests.
  DA to reg should give the same result [\/]     
    +++ OK, passed 100 tests; 84 discarded.
  NA to reg should give the same result [\/]     
    +++ OK, passed 100 tests; 84 discarded.

Finished in 6.8299 seconds
5 examples, 0 failures
\end{showCode}


% To run the tests, use \verb|stack test|.

% To also find out which part of your program is actually used for these tests,
% run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
% report for ... is available at ... .html'' and open this file in your browser.
% See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.
>>>>>>> Stashed changes

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.
