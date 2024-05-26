\section{Basic Library}\label{sec:Basics}

\subsection{The Alphabet}\label{subsec:alphabet}

In this section we define our most basic data structure: a finite input alphabet. Our current implementation choice is to record alphabet as a \emph{type class}, equipped with a complete list of symbols:

\begin{code}
module Basics where

import Data.List ( sort )
import Test.QuickCheck ( elements, Arbitrary(arbitrary) )

class Ord a => Alphabet a where
  completeList :: [a]
\end{code}

The reason for this implementation choice is that we can silently pass this recorded list of complete alphabet as input via constraint declarations. We also require any alphabet shall be ordered.

Here is an example: The function \texttt{alphIter} will check if a list contains exactly each element of the alphabet once. This function will be useful when we work with deterministic automata.

\begin{code}
alphIter :: Alphabet a => [a] -> Bool
alphIter l = sort l == completeList 
\end{code}

The main input alphabet we are going to use on testing consists of three letters. This choice is of course not essential to our main implementation, which will be parametric over all type instances of the class \texttt{Alphabet}.

\begin{code}
data Letter = A | B | C deriving (Eq, Ord)

instance Show Letter where
  show A = "a"
  show B = "b"
  show C = "c"

instance Alphabet Letter where
  completeList = [A,B,C]
\end{code}

To use the QuickCheck library to test on arbitrary inputs, we also define the type \texttt{Letter} as an \texttt{Arbitrary} instance:

\begin{code}
instance Arbitrary Letter where
  arbitrary = elements completeList
\end{code}


