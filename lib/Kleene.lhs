
We have now defined (non)deterministic automata and regular expressions. 
Next, perhaps unsurprisingly, since these are well known to be two sides of the same coin, we encode a method to translate between them.
Converting from a regex to a non-deterministic automaton is relatively straightforward, so we will begin with that.
Second, we will describe Kleene's algorithm (a variation of the Floyd-Warshall Algorithm) in order to transform an automaton into a regex.
Finally, we will note general problems with the above two steps as well as possible future methods to improve them.

\begin{code}
module Kleene where

import Alphabet   ( Alphabet(..) )
import Automata   ( AutData(..), NDetAut(..), encodeNA, trsOf )
import Regex      ( Regex(..), simplifyRegex, altList, seqList )
import Data.Maybe ( fromJust, isNothing )

import qualified Data.Map.Strict as Map

type RgxAutData l = (AutData l Int, Int)
\end{code}

\subsection{Regular Expressions to Automata}

Converting a regular expression into a non-deterministic automaton is both straightforward and (mostly) intuitive. 
Because regular expressions are defined inductively, we can associate an automaton with each base case, and then associate methods for combining automata for inductive cases.
At a high level we can think of our algorithm as follows: first, the transition labels correspond to our alphabet; 
second, generate a very simple automaton for each atom (letter, epsilon, or empty string); 
then attach these automata together in a well-behaved way for each operator. 
Roughly, \texttt{Seq} corresponds to placing each automaton one after the other, \texttt{Alt} to placing them in parallel, and \texttt{Star} to folding the automaton into a circle. 
We will explain each of these operations more clearly in the appropriate section.
As for any inductive construction we start with our base cases. Note these choices are not unique (there are many automata that accept no words) but we go with the simplest ones for each case:
\begin{align*}
  &\texttt{Empty}: \text{ a single, non-accepting, state.} \\
  &\texttt{Epsilon}: \text{ a single, accepting, state.} \\
  &\texttt{L a}: \text{ a non-accepting state, connected to an accepting one by $a$}
\end{align*}
\begin{code}
regToAut :: Regex l -> RgxAutData l
-- gives an integer automata and a starting state
regToAut Empty = (AD [1] [] [], 1)
regToAut Epsilon = (AD [1] [1] [], 1)
regToAut (L l) = (AD [1,2] [2] [(1, [(Just l,2)])], 1) 
regToAut (Seq a b) = seqRegAut (regToAut a) (regToAut b)
regToAut (Alt a b) = altRegAut (regToAut a) (regToAut b)
regToAut (Star a)  = starRegAut $ regToAut a

-- convenience function for encoding result directly to an NA
fromReg :: (Alphabet l) => Regex l -> (NDetAut l Int, Int)
fromReg reg = (encodeNA ndata,st)
  where (ndata,st) = regToAut reg
\end{code}

An observant reader will have noticed this outputs an automata with \texttt{Int} states; this simply makes it easy to recurisvely generate new state labels in a well-bheaved way.

\begin{code}

seqRegAut :: RgxAutData l -> RgxAutData l -> RgxAutData l
seqRegAut (aut1,s1) (aut2,s2) = 
  (adata, 13*s1) where
  adata = AD 
    ([ x*13 | x <- stateData aut1 ] ++ [ x*3 | x <- stateData aut2 ]) -- states
     [ 3*x | x <- acceptData aut2 ]                                   -- accepting
     (gluingSeq (aut1, s1) (aut2, s2))                                -- transitions

gluingSeq :: RgxAutData l -> RgxAutData l -> [(Int, [(Maybe l, Int)])]
gluingSeq (aut1, _) (aut2, s2) =  fstAut ++ mid ++ sndAut where
  fstAut = [mulAut 13 x (aut1 `trsOf` x) | x <- stateData aut1, x `notElem` acceptData aut1]
  mid = [appTuple (mulAut 13 x (aut1 `trsOf` x)) (Nothing,3*s2) | x <- acceptData aut1]
  sndAut = [mulAut 3 x (aut2 `trsOf` x) | x <- stateData aut2]  
  mulAut n x trs = (x*n, multTuple n trs)
  appTuple (n,tr) t = (n,tr++[t])
\end{code}

This function takes two automata \texttt{aut1,aut2} and glues them together by adding epsilon transitions between the accepting states of \texttt{aut1} and the starting state of \texttt{aut2}.
We need to add these epsilon transitions rather than merely identify the starting/ending in order to preserve transitions out of said states.
For example, if we identify states 1 and 2 in the following two automata (blue states being intial, orange being accepting):
\[\begin{tikzcd}[ampersand replacement=\&]
	\textcolor{rgb,255:red,92;green,92;blue,214}{2} \&\& \textcolor{rgb,255:red,214;green,153;blue,92}{3} \\
	\textcolor{rgb,255:red,92;green,92;blue,214}{0} \&\& \textcolor{rgb,255:red,214;green,153;blue,92}{1}
	\arrow["a", from=1-1, to=1-1, loop, in=55, out=125, distance=10mm]
	\arrow["b", from=1-1, to=1-3]
	\arrow["a", from=2-1, to=2-3]
	\arrow["b"', from=2-3, to=2-3, loop, in=305, out=235, distance=10mm]
\end{tikzcd}\]
we would change the language from $ab^*a^*b$ to $a(b^*a^*)^*b$. Thus, we add epsilon transitions.

Additionally, we multiply the states in the first automaton by 13 and states in the second automaton by 3.
In the gluing and star operator we have to add new states (in order to prevent the gluing issue above). 
We always add a state labeled $1$ for a starting state and $2$ for an accepting state.
Multiplication by prime numbers allows us to ensure that our new automaton \textit{both} preserves the transition function of its component parts \textit{and} has distinct state labels for every state.
The primes are chosen arbitrarily, they simply ensure that each state has a unique label and allow us to understand which operations have been applied to which states for bugetsting-purposes.
 
\begin{code}
altRegAut :: RgxAutData l -> RgxAutData l -> RgxAutData l
altRegAut (aut1, s1) (aut2, s2) = 
  (adata, 1) where
  adata =  AD 
    ([1,2] ++ [ x*5 | x<- stateData aut1 ] ++ [ x*7 | x<- stateData aut2 ])
    [2] 
    (gluingAlt (aut1, s1) (aut2, s2))

gluingAlt :: RgxAutData l -> RgxAutData l -> [(Int, [(Maybe l, Int)])]
gluingAlt (aut1,s1) (aut2,s2) = start ++ fstAut ++endFstAut ++ sndAut ++ endSndAut where 
  start = [(1, [(Nothing, s1*5), (Nothing, s2*7)])]
  fstAut = [mulAut 5 x (aut1 `trsOf` x) | x <- nonAccept aut1]
  sndAut = [mulAut 7 x (aut2 `trsOf` x) | x <- nonAccept aut2]
  endFstAut = [appSnd (Nothing,2) (mulAut 5 x (aut1 `trsOf` x)) | x <- acceptData aut1]
  endSndAut = [appSnd (Nothing,2) (mulAut 7 x (aut2 `trsOf` x)) | x <- acceptData aut2]
  mulAut n x trs = (x*n, multTuple n trs)
  nonAccept aut = [ x | x <- stateData aut, x `notElem` acceptData aut ]
  appSnd a (b,c) = (b,a:c)
\end{code}

Our construction for \texttt{Alt} is defined similarly to \texttt{Seq}.
We add a new initial and acceptance state to ensure that our gluing preserves the appropriate transition functions.
Lastly, we define our \texttt{Star} construction as follows (alongside some helper functions):

\begin{code}
starRegAut :: RgxAutData l -> RgxAutData l
starRegAut (aut, s) = 
  (adata, 1) where
  adata = AD 
    (1:[x*11 | x<- stateData aut])
    [1]
    (gluingStar (aut, s))

gluingStar :: RgxAutData l -> [(Int, [(Maybe l, Int)])]
gluingStar (aut1, s1) = start ++ middle ++ end where
  start = [(1, [(Nothing, s1*11)])]
  middle = [(x*11, multTuple 11 (aut1 `trsOf` x))| x<-stateData aut1, x `notElem` acceptData aut1]
  end = [(a*11, (Nothing, 1) : multTuple 11 (aut1 `trsOf` a)) | a <- acceptData aut1]

multTuple :: Int -> [(a,Int)] -> [(a,Int)]
multTuple _ [] = []
multTuple n ((a,b):xs) = (a,n*b) : multTuple n xs

addTuple :: Int -> [(a,Int)] -> [(a,Int)]
addTuple _ [] = []
addTuple n ((a,b):xs) = (a,n+b) : multTuple n xs

\end{code}
For \texttt{Star} we add a single state which serves as both the initial state and an accept state. 
By connecting the beginning and ending of our starting automaton we create an abstract loop---corresponding to the operation \texttt{Star}.

This construction was relatively straightforward since by looking at what each operator in a regular expression means an automaton immediately suggests itself.
The next algorithm, moving from automata to regular expressions, is far less intuitive, and encounters difficulties we will note in the final section.
This complexity is due to the non-inductive/recursive definition of automata as opposed to regex.

\subsection{Automata to Regular Expressions}\label{subsec:kalgo}

Here, we implement an algorithim which take a non/deterministic automaton, a starting state, and outputs a corresponding regular expression.
The algorithm we use, called Kleene's algorithm, allows us to impose a semi-recursive structure on an automaton which in turn allows us to extract a regular expression.
First, we provide the implement of Kleene's algorithm (as well as some motivation and examples) before explaining how Kleene's algorithm can provide us with our desired conversion.
We conclude with a brief overview of the helper functions we enlist throughout our implementation as well as a slightly different conversion (and why we opted with our method.)

Below, you will find our implementation of Kleene's algorithm;
it take an automaton (whose states are labeled $[0 . . n]$ exactly), and three integers $i,j,k$ (which correspond to states) and outputs a regular expression corresponding to the set of all paths from state $i$ to state $j$ without passing through states higher than $k$.
The integer labels allow us to define a recursive function and it is easy to relabel states like this.

\begin{code}
kleeneAlgo :: Eq l => AutData l Int -> Int -> Int -> Int -> Regex l 
kleeneAlgo aut i j (-1) = 
  if i==j 
  then simplifyRegex (Alt Epsilon (altList [ maybe Epsilon L a | a <- successorSet aut i j]))
  else simplifyRegex (altList [ maybe Epsilon L a | a <- successorSet aut i j])
kleeneAlgo aut i j k = 
  simplifyRegex (Alt (simplifyRegex $ kleeneAlgo aut i j (k-1)) 
                     (simplifyRegex $ seqList
                              [ simplifyRegex $ kleeneAlgo aut i k (k-1)
                              , simplifyRegex $ Star $ kleeneAlgo aut k k (k-1)
                              , simplifyRegex $ kleeneAlgo aut k j (k-1) ]))
\end{code}
Let us quickly dig in what this code actually means before moving on to an example.
The algorithm successively removes states by decrementing $k$.
At each step we remove the highest state and nicely add its associate transition labels to the remaining states.
If \texttt{regToAut} worked by building up an automaton to follow a regular expression, Kleene's algorithm works by pulling a fully glued automaton apart step by step.
When $k=-1$, we want to return a regex corresponding to the set of paths from $i$ directly to $j$ without stopping at any either state along the way.
This is simply the set of transition labels which connect $i$ to $j$ (alongside \texttt{Epsilon} if $i=j$.)
However, if $k>-1$, we need to remove the $k$'th state and shift the transition functions into and out of $k$ amidst the rest of the automaton.
First, we don't touch any of the paths which avoid $k$ by including $\texttt{kleeneAlgo} \ \texttt{aut} \ i \ j \ (k-1)$.
The remaining sequence can be viewed as: take any path to you want to $k$ but stop \textit{as soon as} you reach $k$ for the first time;
then, take any path from $k$ to $k$ as many times as you want;
finally, take any path from $k$ to $j$.

As we will see in the following example, this entire process can be though of as a single transition label encoding all of the data that used to be at $k$.
By removing every state, we are left with a single arrow which corresponds to our desired regular expression.
It is important to note that the algorithim does not \textit{actually} change the autaumaton - rather this is a useful description of the recursive process the algorithim goes through.

In the following toy example, we apply the algorithim to this automata with intial state $0$ and accepting state $1$:
\[\begin{tikzcd}[ampersand replacement=\&]
	\& 2 \\
	\textcolor{rgb,255:red,92;green,92;blue,214}{0} \&\& \textcolor{rgb,255:red,214;green,153;blue,92}{1}
	\arrow["b", from=1-2, to=2-3]
	\arrow["a", from=2-1, to=1-2]
	\arrow["a"', from=2-1, to=2-3]
\end{tikzcd}\]

We apply the algorithim to $0$ (the starting state) $1$ (the accepting state) and $2$ (the largest state.) 
By removing $2$ from the state space (which is what decrementing $k$ does), we get
\[(a\epsilon^*b)+a\]
which is exactly what the regular expression corresponding to this automaton is. 
Hopefully this very simple example has highlighted the motivation and process behind the algorithim.

With this broad motivation, we can know discuss how to implement the algorithm to provide our desired conversion:
\begin{code}
autToReg :: Eq l => Ord s => (AutData l s, s)-> Regex l
autToReg (aut, s)= altList [kleeneAlgo intAut firstState a lastState | a <- acceptData intAut] where 
  intAut = fst $ relabelAut (aut,s)
  firstState = relabelHelp aut s
  lastState = length (stateData intAut) - 1


\end{code}
This takes an automaton (and a starting state), transforms that automaton into one with the appropriate state labels and then applies the algorithm on the initial state and every accepting state.
For a given accepting state $a$, $(\texttt{kleeneAlgo} \ \texttt{aut} \  \text{firstState} \ a$ lastState) provides a regular expression corresponding to the paths from the initial state to $a$ with no restrictions - we have set $k$ to be higher than every state label.
This is exactly what we were looking for, given our previous understanding of the algorithm itself.

Below we briefly describe the helper functions needed for this implementation as well as an alternate definition of autToReg, whose problems we will expound upon in the last section of this chapter.
First, this function simply returns returns all the ways to directly move between two states for the base case of Kleene's algorithm.
\begin{code}
-- takes automata data and states s1, s2. Outputs all the ways to get s2 from s1
successorSet :: Eq s => AutData l s -> s -> s -> [Maybe l]
successorSet aut s1 s2 
  | isNothing (lookup s1 (transitionData aut) ) = [] -- if there are no successors
  | otherwise = map fst (filter (\w -> s2 == snd w) (fromJust $ lookup s1 (transitionData aut)) )
\end{code}
Additionally, as mentioned, we need to convert an arbitrary automaton to one with well-behaved state labels in order to define Kleene's algorithm. 
These functions do so handily via the use of a dictionary.
\begin{code}
-- states as integer makes everything easier. We use a dictionary to relabel in one sweep per say
relabelHelp :: Ord s => AutData l s -> s -> Int
relabelHelp aut s = fromJust (Map.lookup s (Map.fromList $ zip (stateData aut) [0 .. (length (stateData aut))]))

relabelAut :: Ord s => (AutData l s, s) -> RgxAutData l
relabelAut (aut, s1) = (AD [relabelHelp aut s | s <- stateData aut]
                           [relabelHelp aut s| s<- acceptData aut]
                           [(relabelHelp aut s, [ (a, relabelHelp aut b)| (a,b) <- aut `trsOf` s] ) | s<- stateData aut]
                       , relabelHelp aut s1)

\end{code}



\subsection{Issues with the Algorithms}

The most prominent issue with this algoritihm is that it creates very complex regular expressions---each step adds a \texttt{Seq}, \texttt{Alt}, and \texttt{Star}.
We have attempted to implement a few simplification throughout the algorithm, but it still outputs expressions that are horribly over-complex. For example,
\begin{align*}
&\texttt{autToReg}  \ (\texttt{wikiAutData}, 0) = \\ 
&\quad b+c+((\epsilon +a)(a^*)(b+c))+ \\
&\quad\quad ((b+c+((\epsilon +a)(a^*)(b+c))) (\epsilon +b+((a+c)(a^*)(b+c)))^* (\epsilon +b+((a+c)(a^*)(b+c))))
\end{align*}
which, upon manual reduction, is equivalent to
\[ (a+c)^*b(b+c+a(a+c)^*b)^* \]
However, reduction of regular expressions is \textsf{NP}-hard, and so we have simply tried to encode a few, computationally quick, simplifications as noted in Section~\ref{sec:Regex}.
This is most pressing when we convert back into an automaton, since each new operator corresponds to an additional structural level in the automaton and an additional complication when running words on automata.
There are several ways this could be improved.
Perhaps most straightforward would be to further improve our regular expression simplifcation---or change the type definition to more easily manage commutativity.
Another possibility would be to implement other algorithms aside from Kleene's which might be better-fit for converting certain automata, comparing results across them.
Finally, we could implement automaton-minimisation.
