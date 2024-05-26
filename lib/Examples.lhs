\section{Examples and Testing}\label{sec:Examples}

In this section we define several examples of (non)deterministic automata and regular expressions, and run tests on them to verify the correctness of our algorithm written earlier. More concretely, we would like to test:
\begin{itemize}
\item All the basic semantic layers for (non)deterministic automata and regular expressions should be correctly working.
\item The conversion between deterministic and non-deterministic automata implemented in Section~\ref{sec:Automata} should be behaviourally equivalent. 
\item The conversion between (non)deterministic automata and regular expressions implemented in Section~\ref{sec:DetAut} should be behaviourally equivalent.
\end{itemize}

\subsection{Examples of Automata and Regular Expressions}\label{subsec:examples}

We begin by including the relevant modules.
\begin{code}
module Examples where

import Basics ( Letter(..) )
import Automata
    ( NDetAut,
      DetAut,
      AutData(AD),
      detCheck,
      encodeDA,
      run,
      acceptDA,
      encodeNA,
      decode,
      runNA,
      ndautAccept )
import Regex ( Regex(..) )
import Kleene ( autToReg, dautToReg )
import Data.Maybe ( fromJust )
\end{code}

Some examples of deterministic automata:
\begin{code}
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

myDAtoReg :: Regex Letter
myDAtoReg = dautToReg myDA 1

wikiAutData :: AutData Letter Int -- automata taken from Wikipedia Page on Kleenes Algorihtim
wikiAutData = AD [0,1]
                 [1]
                 [(0, [(Just A, 0)
                      ,(Just B, 1)
                      ,(Just C, 1)])
                 ,(1, [(Just A, 0)
                      ,(Just B, 1)
                      ,(Just C, 0)])]

wikiDA :: DetAut Letter Int
wikiDA = fromJust $ encodeDA wikiAutData

wikiDAtoReg :: Regex Letter
wikiDAtoReg = dautToReg wikiDA 0
\end{code}

By manually checking, the following should be an accepting input for \texttt{myDA}.
\begin{code}
-- an accepting sequence of inputs
myInputs :: [Letter]
myInputs = [A,A,A,A,B,C,B,B,B,A]

myTestRun :: (Int, Bool)
myTestRun = (finalst, result)
  where finalst = run myDA 1 myInputs
        result = acceptDA myDA 1 myInputs
\end{code}

Let us also consider examples of a non-deterministic automaton:
\begin{code}
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
\end{code}

Again, some simple cases to ensure basic performance:

\begin{code}
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
\end{code}

Using the Kleene algorithm in Section~\ref{sec:DetAut}, we should be able to transform the non-deterministic automaton to regular expressions:

\begin{code}
myNDAtoReg :: Regex Letter
myNDAtoReg = autToReg (decode myNDA, 1)
\end{code}

Here are also some examples for regular expressions:
\begin{code}
exampleRegex :: Regex Letter
exampleRegex = Star (Alt (L A) (L B))

annoyingRegex :: Regex Letter
annoyingRegex = Alt Empty (Seq Epsilon (L A))
\end{code}
