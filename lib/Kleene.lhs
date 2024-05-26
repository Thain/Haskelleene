
\section{Automata and Regular Expressions}\label{sec:DetAut}

We previously have defined non/determinisitc automata and regular expressions. 
Next, perhaps unsuprisingly, since these are well known to be two sides of the same coin, we encode a method to transfer between them.
\textbf{Possible to do:} and prove these operations are inverses of each other.
Converting froma regex to a non-deterministic automaton is relatively straightforward, so we begin with that.
Second, we describe Kleene's Algorithim (a variation of the Floyd-Warshall Algorithim) in order to transform an automaton into a regex.
Finally, we note general problems with the above two steps as well as possible future methods to improve them.

\subsection{Regular Expressions to Automata}

Converting a regular expression into a non-dterminsitic automaton is both straightforward and (mostly) intuitive. 
We have defined a regular expression using an inductive constructor, similar to propositional logic. 
This inductive construction readily allows us to recursive construct this an automaton - with one general construction per regex operator.
At a high level we can think of our algorithim as follows: first, the transition labels correspond to our alphabet; 
second, generate a very simple automaton for each atom (letter, epsilon, or empty string); 
then attach these automata together in a well-behaved way for each operator. 
Roughly, sequence corresponds to placing each automaton one after the other, alternate to placing them in parralel, and star to folding the automaton into a circle. 
We will explain each of these operations more clearly at the appropriate section.
As for any inductive construction we need our base cases, which, for a regular expression are: the Empty expression, the Epislon expression, and a single letter. 
The simplest NDA which accepts no words is a single node with no accept states, a single node with a single accepting state accepts the empty word, and two nodes connected by a transition function labeled with our letter accepts said single letter.

\begin{code}
module Kleene where

import Basics      -- contains all of our utility functions
import Automata    -- contains automaton definitions/conversions
import Regex       -- contains regex definitions
import Data.Maybe

import qualified Data.Map.Strict as Map

-- ---------------
-- REGEX to DetAut
-- ---------------

-- Since regex to automata inducts on the transition functions, we need a way to glue or reshape our automata nicely
-- As we add more states we need to relable them. The base states are 1 and 2, multiplying by 3, 13 is sequence, multiplying by 5 and 7 is Alt, multiplying by 11 is Star

--useful function to glue states together


-- For each operator we define two corresponding functions. One outputs the automata data associated with that operator, 
-- the other stitches and modifies the transition function across the inputs automata (mostly using Epsilon transitions)

regToAut :: Regex l -> (AutData l Int, Int) 
-- gives an integer automata and a starting state
regToAut Empty = (AD [1] [] [], 1)
regToAut Epsilon = (AD [1] [1] [], 1)
regToAut (L l) = (AD [1,2] [2] [(1, [(Just l,2)])], 1) 
regToAut (Seq a b) = seqRegAut (regToAut a) (regToAut b)
regToAut (Alt a b) = altRegAut (regToAut a) (regToAut b)
regToAut (Star a)  = starRegAut $ regToAut a

fromReg :: (Alphabet l) => Regex l -> (NDetAut l Int, Int)
fromReg reg = (encodeNA ndata,st)
  where (ndata,st) = regToAut reg

\end{code}

As we had into each inductive step, we note a few conventions. 
First, an observant reader will have seen that our function outputs automata data with integer states. 
Since we are inductively constructing automata we need to be adding new states while preserving the old ones (and their transition functions).
Integer states make it very easy to relable them, and - as we will see later - make it much easier to run algorithims on.
Below, you can see our function for the Seq operator alongside a helpful fetch function.

\begin{code}

seqRegAut :: (AutData l Int, Int) -> 
             (AutData l Int, Int) -> 
             (AutData l Int, Int)
seqRegAut (aut1,s1) (aut2,s2) = 
  ( AD 
    ([ x*13 | x <- stateData aut1 ] ++ [ x*3 | x <- stateData aut2 ]) -- states
    [ 3*x | x <- acceptData aut2 ] -- accepting states
    (gluingSeq (aut1, s1) (aut2, s2)) -- transition function
  , 13*s1) -- starting state

gluingSeq :: (AutData l Int, Int) -> (AutData l Int, Int) -> 
             [(Int, [(Maybe l, Int)])]
gluingSeq (aut1, _) (aut2, s2) =  firstAut ++ middle ++ secondAut where
  firstAut = [(13*x, multTuple 13 (transForState aut1 x)) | x<- stateData aut1, x `notElem` acceptData aut1]
  middle = [(13*x, multTuple 13 (transForState aut1 x) ++ [(Nothing, 3*s2)]) | x<- acceptData aut1]
  secondAut = [(x*3, multTuple 3 (transForState aut2 x)) | x<- stateData aut2]

transForState :: Eq s => AutData l s -> s -> [(Maybe l, s)]
transForState aut s 
  | isNothing $ lookup s $ transitionData aut = []
  | otherwise = fromJust $ lookup s $ transitionData aut
\end{code}

This functoion takes two automata $aut1,aut2$ and glues them together by adding epsilon transitions between the accepting states of $aut1$ and the starting state of $aut2.$
We need to add these epsilon transitions rather than merely identify the starting/ending in order to preserve tranitions out of said states.
For example, if we glued the start/accepting states together in the following automaton DIAGRAM
we would accept abaa, where FINISH EXAMPLE.
Additionally, we multiply the states in the first automaton by 13 and states in the second automaton by 3.
In the gluing and star operator we have to add new states (in order to prevent the gluing issue above). 
We always add a state labeled $1$ for a starting state and $2$ for an accepting state.
Multiplication by prime numbers allows us to ensure that our new automaton \textit{both} preserves the transition function of its component parts \textit{and} had distinct state labels for every state.
Each input for each operator has a unique prime number assigned to it:
\begin{enumerate}
\item Sequence: $13,3$
\item Alternate: $5,7$
\item Star: $11.$
\end{enumerate}
 



\begin{code}


altRegAut :: (AutData l Int, Int) -> (AutData l Int, Int) -> (AutData l Int, Int)
altRegAut (aut1, s1) (aut2, s2) = 
  ( AD 
    ([1,2] ++ [ x*5 | x<- stateData aut1 ] ++ [ x*7 | x<- stateData aut2 ])
    [2] 
    (gluingAlt (aut1, s1) (aut2, s2))
  , 1 )

gluingAlt :: (AutData l Int, Int)->(AutData l Int, Int) -> 
             [(Int, [(Maybe l, Int)])]
gluingAlt (aut1,s1) (aut2,s2) = start ++ firstAut ++endFirstAut ++ secondAut ++ endSecondAut where
  start = [(1, [(Nothing, s1*5), (Nothing, s2*7)])]
  firstAut = [(x*5, multTuple 5 (transForState aut1 x)) | x <- stateData aut1, x `notElem` acceptData aut1]
  secondAut = [(x*7, multTuple 7 (transForState aut2 x)) | x <- stateData aut2, x `notElem` acceptData aut2]
  endFirstAut = [(x*5, (Nothing,2) : multTuple 5 (transForState aut1 x)) | x <- acceptData aut1]
  endSecondAut = [(x*7, (Nothing,2) : multTuple 7 (transForState aut2 x)) | x <- acceptData aut2]
\end{code}

Our construction for alternate is defined similarly to Sequence.
We add a new initial and acceptance state to ensure that our gluing preserves the appropriate transition functions.
Lastly, we define our Star construction as follows (alongside some helper functions):

\begin{code}
starRegAut :: (AutData l Int, Int) -> (AutData l Int,Int)
starRegAut (aut, s) = 
  ( AD 
    (1:[x*11 | x<- stateData aut])
    [1]
    (gluingStar (aut, s))
  , 1)

gluingStar :: (AutData l Int, Int)-> [(Int, [(Maybe l, Int)])]
gluingStar (aut1, s1) = start ++ middle ++ end where
  start = [(1, [(Nothing, s1*11)])]
  middle = [(x*11, multTuple 11 (transForState aut1 x))| x<-stateData aut1, x `notElem` acceptData aut1]
  end = [(a*11, (Nothing, 1) : multTuple 11 (transForState aut1 a)) | a <- acceptData aut1]

multTuple :: Int -> [(a,Int)] -> [(a,Int)]
multTuple _ [] = []
multTuple n ((a,b):xs) = (a,n*b) : multTuple n xs

addTuple :: Int -> [(a,Int)] -> [(a,Int)]
addTuple _ [] = []
addTuple n ((a,b):xs) = (a,n+b) : multTuple n xs

\end{code}
For Star we add a single node which serves as both the intitial state and an accept state. 
By connecting the beginning and ending of our starting automaton we create an abstract loop - which clearly corresponds to Star.
Now that we have defined each construction, we provide a brief proof of the following lemma:

\begin{lemma}
  Each regular expression $r$ gives rise to (at least one) non-deterministic automaton, $D,$ such that
  \[L(r) = L(D).\]
\end{lemma}

\begin{proof}
Let $r$ be an arbitrary regular expression and set $aut=(fst.fromReg) r.$ First, consider some $w \in L(r)$ and proceed via induction to show that $w\in L(aut).$

We believe the base cases are clear from construction and so move one



\end{proof}

This construction was relatively straightforward since by looking at what each operator in a regular expression means an automaton immediately suggests itself.
The next algorithim, moving from automata to regular expressions, is far less intuitive, and encounters difficulties we will note in the final section.
This complexity is due to the non-inductive/recurisve definition of automata as opposed to regex.

\subsection{Automata to Regular}

Here, we implement which take a non/determinisitc automaton, a starting state, and ouputs a corresponding regular expression.
The algorithim we use, called Kleene's Algorithim, allows us to impose a semi-recusrive structure on an automaton which in turn allows us to extract a regular expression.
First, we provide the implement of Kleene's Algorithim (as well as some motivation and examples) before explaining how Kleene's Algorithim can provide us with our desired conversion.
We conclude with a brief overview of the helper functions we enlist throughout our implementation as well as a slightly different conversion (and why we opted with our method.)

\subsubsection{Kleene's Algorithim}

Below, you will find our implementation of Kleene's Algorithim;
it take an automaton (whose states are labelled $[0 . . n]$ exactly), and three integer $i,j,k$ (which correspond to states) and 
outputs a regular expression corresponding to the set of all paths from state $i$ to state $j$ without passing through states higher than $k$.
This is a rather strong structural requirement, but it allows us to define the algorithim recurivsely and - as we will show later in the report - it is easy to convert any automaton into one with the correct state labels.

\begin{code}
kleeneAlgo:: Eq l => AutData l Int -> Int -> Int -> Int -> Regex l
kleeneAlgo aut i j (-1) = 
  if i==j 
  then simplifyRegex (Alt Epsilon (altList [ maybe Epsilon L a | a <- successorSet aut i j]))
  else simplifyRegex (altList [ maybe Epsilon L a | a <- successorSet aut i j])
kleeneAlgo aut i j k = 
  simplifyRegex (Alt (simplifyRegex $ kleeneAlgo aut i j (k-1)) 
                     (simplifyRegex $ seqList [ simplifyRegex $ kleeneAlgo aut i k (k-1)
                                              , simplifyRegex $ Star $ kleeneAlgo aut k k (k-1)
                                              , simplifyRegex $ kleeneAlgo aut k j (k-1) ]))
\end{code}
Let us quickly dig in what this code actually means before moving onto an example.
The algoritihim succsessively removes states by incrementing $k$ downwards.
At each step we remove the highest state and nicely add its associate transition labels to the remaining states.
If our regex to automata algoritihm worked by building up an automaton to follow a regular expression, Kleene's Algorithm works by pulling a fully glued automaton apart step by step.
When $k=-1$, we want to return a regex corresponding to the set of paths from $i$ directly to $j$ without stopping at any either state along the way.
This is simply the set of transition labels which connect $i$ to $j$ (alongside Epsilon if $i=j$.)
However, if $k>-1$, we need to remove the $k$'th state and shift the transition functions into and out of $k$ amidst the rest of the automaton.
First, we don't touch any of the paths which avoid $k$ by including $kleeneAlgo aut i j (k-1).$
The remaining sequence can be viewed as: take any path to you want to $k$ but stop \textit{as soon as} you reach $k$ for the first time;
then, take any path from $k$ to $k$ as many times as you want (we need the Star here because this algorithim does not normally permit loops);
finally, take any path from $k$ to $j.$
As we will see in the following example, this entire process can be though of as a single transition lable encoding all of the data that used to be at $k.$
By removing every state, we are left with a single arrow which corresponds to our desired regular expression.

TIKZ EXAMPLE.

With this broad motivation, we can know discuss how to implement the algoritihm to provide our desirec conversion:
\begin{code}
-- Take a collection of data and starting states, outputs a regular expression which corresponds to the language. This version creates a nice first and last state
autToRegSlow :: Eq l => Ord s => (AutData l s, s)-> Regex l
autToRegSlow (aut, s)= kleeneAlgo intAut 0 lastState lastState where 
  intAut = (fst.cleanAutomata.relabelAut) (aut,s)
  lastState = length (stateData intAut) - 1 
--autToReg aut [s]= kleeneAlgo newAut 0 (length stateData aut) (length stateData aut) where newAut = cleanAutomata . relabelAut aut

--This version does not make a nice first and last state (and thus can't be adapted to multiple start states), but cuts down on the epislons
autToReg :: Eq l => Ord s => (AutData l s, s)-> Regex l
autToReg (aut, s)= altList [kleeneAlgo intAut firstState a lastState | a <- acceptData intAut] where 
  intAut = fst $ relabelAut (aut,s)
  firstState = relabelHelp aut s
  lastState = length (stateData intAut) - 1

--following the Wikipedia page, this function recursively removes elements and uses the removed transition lables to construct the regex. 

\end{code}
This takes an automaton (and a starting state), transforms that automaton into one with the appropriate state labels and then applies the algorithim on the intial state and every accepting state.
For a given accepting state $a$, (kleeneAlgo aut firstState $a$ lastState) provides a regular expression corresponding to the paths from the intial state to $a$ with no restrictions - we have set $k$ to be higher than every state label.
This is exactly what we were looking for, given our previous understanding of the algoritihim itself.

Below we briefly describe the helper functions needed for this implementation as well as an alternate definition of autToReg, whose problems we will expound upon in the last section of this chapter.

\begin{code}

-- takes some automata data and two states, s1, s2. Ouputs all the ways to get s2 from s1
successorSet :: Eq s => AutData l s -> s -> s -> [Maybe l]
successorSet aut s1 s2 
  | isNothing (lookup s1 (transitionData aut) ) = [] -- if there are no successors
  | otherwise = map fst (filter (\w -> s2 == snd w) (fromJust $ lookup s1 (transitionData aut)) )
\end{code}
This function simply returns returns all the ways to directly move between two states for the base case of Kleenes Algorithim.
\begin{code}
-- states as integer makes everything easier. We use a dictionary to relabel in one sweep per say
relabelHelp :: Ord s => AutData l s -> s -> Int
relabelHelp aut s = fromJust (Map.lookup s (Map.fromList $ zip (stateData aut) [0 .. (length (stateData aut))]))

relabelAut :: Ord s => (AutData l s, s) -> (AutData l Int, Int)
relabelAut (aut, s1) = (AD [relabelHelp aut s | s <- stateData aut]
                           [relabelHelp aut s| s<- acceptData aut]
                           [(relabelHelp aut s, [ (a, relabelHelp aut b)| (a,b) <- transForState aut s] ) | s<- stateData aut]
                       , relabelHelp aut s1)

\end{code}
As mentioned, we need to convert an arbitrary automaton to one with well-behaved state labels in order to define Kleene's Algorithim. 
These functions do so handily via the use of a dictionary.
\begin{code}
-- take aut data and make a nice start state/end state
cleanAutomata:: (AutData l Int, Int) -> (AutData l Int, Int)
cleanAutomata (aut, s) = (AD (0:lastState:[x+1 | x <- stateData aut])
                             [lastState]
                             (cleanTransition (aut,s))
                         ,0) where lastState = 1+length (stateData aut)
 
cleanTransition:: (AutData l Int, Int) -> [(Int, [(Maybe l, Int)])]
cleanTransition (aut, s) = start ++ middle ++ end where
  start = [(0, [(Nothing, s+1)])]
  middle = [(x+1, addTuple 1 (transForState aut x)) | x <- stateData aut, x `notElem` acceptData aut]
  end = [(x+1, (Nothing, length (stateData aut) + 1) : addTuple 1 (transForState aut x)) | x<- acceptData aut]


\end{code}
These last peices of code allow us to define a version of autToReg which takes in multiple intitial states rather than just one. 
It does so by adding a new intitial (and accepting) state after the relabelling - connected via epsilon transition.
While this construction is more general, it adds several more transitions which further increase the size of the corresponding regular expression.
More on this issue in the following section.
\begin{code}
-- Another implementation of Automata to Reg
-- We assume the automaton is deterministic 

dautToReg :: (Alphabet l, Ord s) => DetAut l s -> s -> Regex l 
dautToReg daut s = simplifyRegex $ foldr (Alt . dautToRegSub daut s (states daut)) Empty $ accept daut

dautToRegSub :: (Alphabet l, Ord s) => DetAut l s -> s -> [s] -> s -> Regex l 
dautToRegSub daut s0 [] sn = if s0 /= sn then resut else Alt Epsilon resut 
  where trans = delta daut
        succs = filter (\l -> trans l s0 == sn) completeList
        resut = foldr (Alt . L) Empty succs
dautToRegSub daut s0 (s1:ss) sn = simplifyRegex $ Alt reg1 $ Seq reg2 $ Seq (Star reg3) reg4
  where reg1 = simplifyRegex $ dautToRegSub daut s0 ss sn
        reg2 = simplifyRegex $ dautToRegSub daut s0 ss s1
        reg3 = simplifyRegex $ dautToRegSub daut s1 ss s1
        reg4 = simplifyRegex $ dautToRegSub daut s1 ss sn



\end{code}

\subsection{Issues with the Algorithims}

Notes on why it took big and why it cant be fixed
