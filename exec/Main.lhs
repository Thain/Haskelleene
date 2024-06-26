\section{Wrapping it up in an exectuable}\label{sec:Main}

We will now use the library form Section \ref{sec:Alphabet} in a program.

\begin{code}
module Main where

main :: IO ()
main = do
  putStrLn "Hello!"
\end{code}

We can run this program with the commands:

\begin{verbatim}
stack build
stack exec myprogram
\end{verbatim}
