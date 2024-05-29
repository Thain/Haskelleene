
\subsection{QuickCheck}\label{sec:QuickCheck}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Test.Hspec ( hspec, describe, it, shouldBe )
import Test.Hspec.QuickCheck ( prop )
import Test.QuickCheck ( (==>) )
import Automata ( acceptDA, decode, fromNA, fromStartNA, ndautAccept )
import Regex ( regexAccept )
import Kleene ( autToReg, dautToReg, fromReg )
import Examples ( exampleRegex, myNDA, myTestRun, wikiDA )

\end{code}

We have tested the following basic facts:
\begin{itemize}
\item A basic running example for a deterministic automaton.
\item The behavioural equivalence of determinisitic and non-deterministic automata under the conversion implemented in Section~\ref{sec:Automata}.
\item The behavioural equivalence of regular expressions and its corresponding non-deterministic automaton implemented in Section~\ref{sec:Kleene}.
\item The behavioural equivalence of a deterministic automaton and its corresponding regular expression implemented in Section~\ref{sec:Kleene}.
\item The behavioural equivalence of a non-deterministic automaton and its corresponding regular expression implemented in Section~\ref{sec:Kleene}.
\end{itemize}

\begin{code}
main :: IO ()
main = hspec $ do
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
