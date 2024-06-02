\subsection{Examples}\label{subsec:Examples}

In this section we define examples of (non)deterministic automata and regular expressions, and run tests to verify correctness of our algorithms. More concretely, we will test:
\begin{itemize}
\item Basic semantic layers for (non)deterministic automata and regular expressions
\item Converting between deterministic and non-deterministic automata (from Section~\ref{sec:Automata})
\item Converting between (non)deterministic automata and regular expressions (from Section~\ref{sec:Kleene})
\end{itemize}

We begin by including the relevant modules.
\begin{code}
module Examples where

import Alphabet ( Letter(..) )
import Automata
    ( AutData(AD), DetAut, NDetAut,
      encodeDA, encodeNA, run, acceptDA )
import Regex ( Regex(..) )
import Data.Maybe ( fromJust )
\end{code}

\begin{tabular}{m{0.6\textwidth} >{\centering}m{2em} m{0.2\textwidth}}
Now we give some examples of automata. Our first is the following deterministic automaton, taken from the Wikipedia page for Kleene's algorithm: & \  & 
\[\begin{tikzcd}
	0 & 1
	\arrow["{a,c}", from=1-1, to=1-1, loop, in=145, out=215, distance=10mm]
	\arrow["b"{description}, curve={height=-6pt}, from=1-1, to=1-2]
	\arrow["a"{description}, curve={height=-6pt}, from=1-2, to=1-1]
	\arrow["{b,c}", from=1-2, to=1-2, loop, in=325, out=35, distance=10mm]
\end{tikzcd}\]
\end{tabular}

\begin{code}
wikiAutData :: AutData Letter Int
wikiAutData = AD [0,1]   -- the states
                 [1]     -- the accepting state
                 [(0, [(Just A, 0) ,(Just B, 1) ,(Just C, 0)]) -- transitions
                 ,(1, [(Just A, 0) ,(Just B, 1) ,(Just C, 1)])]

wikiDA :: DetAut Letter Int
wikiDA = fromJust $ encodeDA wikiAutData
\end{code}

\begin{tabular}{m{0.6\textwidth} >{\centering}m{2em} m{0.2\textwidth}}
We also consider this example of a non-deterministic automaton. Note how the data is not formatted properly: transitions from state 1 are not all listed together, and there are unnecessary epsilon loops that will make our implmementation of NA semantics loop. When encoding this automaton, we will fix these formatting issues: see Section~\ref{sec:Automata} for details.  & \quad & \[\begin{tikzcd}
	1 && 2 \\
	\\
	3 && 4
	\arrow["\epsilon", from=1-1, to=1-1, loop, in=55, out=125, distance=10mm]
	\arrow["{\epsilon, a}", curve={height=-6pt}, from=1-1, to=1-3]
	\arrow["{c,a,\epsilon}"', curve={height=6pt}, from=1-1, to=3-1]
	\arrow["a"', from=1-1, to=3-3]
	\arrow["{\epsilon, c}", curve={height=-6pt}, from=1-3, to=1-1]
	\arrow["b", from=1-3, to=1-3, loop, in=55, out=125, distance=10mm]
	\arrow["\epsilon", curve={height=-6pt}, from=1-3, to=3-3]
	\arrow["a"', curve={height=6pt}, from=3-1, to=1-1]
	\arrow["c"', from=3-1, to=3-1, loop, in=305, out=235, distance=10mm]
	\arrow["c", curve={height=-6pt}, from=3-3, to=1-3]
	\arrow["{b,c}"', from=3-3, to=3-3, loop, in=305, out=235, distance=10mm]
\end{tikzcd}\]
\end{tabular}

\begin{code}
myNAutData :: AutData Letter Int
myNAutData = AD [1,2,3,4]         -- the states
                [4]               -- accepting states
                [(1,[(Nothing,2),(Just C,3)])
                ,(2,[(Nothing,1),(Nothing,4),(Just B,2),(Just C,1)])
                -- want to merge these with above
                ,(1,[(Just A,2),(Just A,3),(Nothing,1),(Nothing,3),(Just A,4)])
                ,(3,[(Just A,1),(Just C,3)])
                ,(4,[(Just B,4),(Just C,4)])]

myNDA :: NDetAut Letter Int
myNDA = encodeNA myNAutData -- this automaton, encoded
\end{code}
Here is an example for regular expressions:
\begin{code}
exampleRegex :: Regex Letter
exampleRegex = Seq (Star (Alt (L A) (L B))) (Alt (Star (L A)) (Alt Epsilon (L B)))
-- pPrints as (a+b)*(a*+Ep+b)
\end{code}
 
