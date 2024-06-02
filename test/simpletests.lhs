
\subsection{QuickCheck}\label{sec:QuickCheck}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Test.Hspec ( hspec, describe )
import Test.Hspec.QuickCheck ( prop )
import Automata ( acceptDA, decode, fromDA, acceptNA, dtdAccept )
import Regex ( regexAccept )
import Kleene ( autToReg, fromReg )
import Examples ( exampleRegex, myNDA, wikiDA )

\end{code}

We have tested behavioural equivalence using randomly generated words. We use a regex, a DA, and an NA as starting points, convert them using one of our functions, and compare the semantics of the original with the new version.
 
\begin{code}
main :: IO ()
main = hspec $ do
  describe "Examples" $ do
    prop "NA and transfer to DA should give the same result" $
      \input -> acceptNA myNDA 1 input == dtdAccept myNDA 1 input
    prop "reg to NA should give the same result" $
      \input -> regexAccept exampleRegex input == uncurry acceptNA (fromReg exampleRegex) input
    prop "DA to reg should give the same result" $
      \input -> acceptDA wikiDA 0 input == regexAccept (autToReg ((decode . fromDA) wikiDA, 0)) input
    prop "NA to reg should give the same result" $
      \input -> acceptNA myNDA 1 input == regexAccept (autToReg (decode myNDA, 1)) input
\end{code}

The result is recorded below. In the beta version of this report, we had to restrict the input size for some cases, but optimisations to the NA semantics made since then have made the limit unnecessary; and we managed to cut our benchmark time in half, too. The main optimisation was to move from tracking active states with a list to using a \texttt{Set}, cutting down on redundant work, and fixing a bug that allowd for infinite looping.

\begin{showCode}
Examples
  NA and transfer to DA should give the same result [\/]
    +++ OK, passed 100 tests.
  reg to NA should give the same result [\/]
    +++ OK, passed 100 tests.
  DA to reg should give the same result [\/]
    +++ OK, passed 100 tests.
  NA to reg should give the same result [\/]
    +++ OK, passed 100 tests.

Finished in 3.6397 seconds
4 examples, 0 failures
\end{showCode}
