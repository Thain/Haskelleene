
\subsection{QuickCheck}\label{sec:QuickCheck}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

-- import Data.Maybe
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
-- import Basics
import Automata
import Regex
import Kleene
import Examples
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

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

% To run the tests, use \verb|stack test|.

% To also find out which part of your program is actually used for these tests,
% run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
% report for ... is available at ... .html'' and open this file in your browser.
% See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.

