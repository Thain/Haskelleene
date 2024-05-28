\section{Testing}\label{sec:Testing}

\subsection{Examples}\label{subsec:Examples}

In this section we define several examples of (non)deterministic automata and regular expressions, and run tests on them to verify the correctness of our algorithms written earlier. More concretely, we would like to test:
\begin{itemize}
\item All the basic semantic layers for (non)deterministic automata and regular expressions should be correctly working.
\item The conversion between deterministic and non-deterministic automata implemented in Section~\ref{sec:Automata} should be behaviourally equivalent. 
\item The conversion between (non)deterministic automata and regular expressions implemented in Section~\ref{sec:Kleene} should be behaviourally equivalent.
\end{itemize}

\subsubsection{Examples of Automata and Regular Expressions}\label{subsubsec:examples}

We begin by including the relevant modules.
\begin{code}
module Examples where

import Alphabet ( Letter(..) )
import Automata
    ( NDetAut,
      DetAut,
      AutData(AD),
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

Now we give some examples of automata. Our first is the following deterministic automaton:
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

myDA :: DetAut Letter Int
myDA = fromJust $ encodeDA myAutData

myDAtoReg :: Regex Letter
myDAtoReg = dautToReg myDA 1

 -- automaton taken from Wikipedia Page on Kleenes Algorihtm
wikiAutData :: AutData Letter Int
wikiAutData = AD [0,1]
                 [1]
                 [(0, [(Just A, 0)
                      ,(Just B, 1)
                      ,(Just C, 0)])
                 ,(1, [(Just A, 0)
                      ,(Just B, 1)
                      ,(Just C, 1)])]

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

Let us also consider this example of a non-deterministic automaton:
\[\begin{tikzcd}
	1 && 2 \\
	\\
	3 && 4
	\arrow["\epsilon", from=1-1, to=1-1, loop, in=55, out=125, distance=10mm]
	\arrow["{\epsilon, a}", curve={height=-6pt}, from=1-1, to=1-3]
	\arrow["{c,a,\epsilon}"', curve={height=6pt}, from=1-1, to=3-1]
	\arrow["a"', from=1-1, to=3-3]
	\arrow["c", curve={height=-6pt}, from=1-3, to=1-1]
	\arrow["b", from=1-3, to=1-3, loop, in=55, out=125, distance=10mm]
	\arrow["\epsilon", curve={height=-6pt}, from=1-3, to=3-3]
	\arrow["a"', curve={height=6pt}, from=3-1, to=1-1]
	\arrow["c"', from=3-1, to=3-1, loop, in=305, out=235, distance=10mm]
	\arrow["c", curve={height=-6pt}, from=3-3, to=1-3]
	\arrow["{b,c}"', from=3-3, to=3-3, loop, in=305, out=235, distance=10mm]
\end{tikzcd}\]
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

-- this automaton, encoded
myNDA :: NDetAut Letter Int
myNDA = encodeNA myNAutData
\end{code}

Again, some simple cases to ensure basic performance:

\begin{code}
myNInputsTrue, myNInputsFalse :: [Letter]
myNInputsFalse = [B,B,A] -- should reject
myNInputsTrue = []       -- should accept 

myNTestRunFalse :: ([([Letter],Int)],Bool)
myNTestRunFalse = (filist,result)
  where filist = runNA myNDA 1 myNInputsFalse
        result = ndautAccept myNDA 1 myNInputsFalse

myNTestRunTrue :: ([([Letter],Int)],Bool)
myNTestRunTrue = (filist,result)
  where filist = runNA myNDA 1 myNInputsTrue
        result = ndautAccept myNDA 1 myNInputsTrue
\end{code}

Using the Kleene algorithm in Section~\ref{sec:Kleene}, we should be able to transform the non-deterministic automaton, and one of its states, into a regular expression.

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
