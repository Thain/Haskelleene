
\subsection{Automata}\label{sec:Automata}

Our first major goal is to implement (non)deterministic automata. Recall that an automaton with input alphabet $\Sigma$ consists of a set of states, a subset of accepting states, and a transition function $\delta$. As input, $\delta$ takes a symbol of the alphabet, and a current state of the automaton. For a deterministic automaton, it outputs a unique next state; For a non-deterministic automaton, it outputs a \emph{list} of possible next states.

\begin{code}
{-# LANGUAGE TupleSections #-}

module Automata where

import Basics ( Alphabet(..), alphIter ) -- contains all of our utility functions
import Data.Maybe ( isJust, fromJust )
import Data.List ( nub )
import qualified Data.Set as Set
\end{code}

However, since $\delta$ of an automaton is a \emph{function}, it is not directly definable as inputs. Our implementation choice is to record the \emph{transition table} of the transition function, and use the following types as an interface of encoding and decoding an automata with finite inputs:

\begin{code}
type TDict l s = [(s, [(Maybe l, s)])]

data AutData l s = AD { stateData :: [s] 
                      , acceptData :: [s] 
                      , transitionData :: TDict l s }
                      deriving Show
\end{code}

Here \texttt{l} should be thought of as the type of the chosen alphabet, while \texttt{s} is the type of our states. The type \texttt{TDict} then acts as the type of transition tables. A pair in \texttt{TDict} should be thought of recoding the information of given a current state, what are the possible output states of a given input. The fact that we have used \texttt{Maybe l} is that we want the type \texttt{AutData} to be simultaneously able to record both deterministic and non-deterministic automata, thus with the possibility of $\epsilon$-transitions. For some examples of using \texttt{AutData} to encode automata, see Section~\ref{sec:Examples}.

A consequence of using the same data type to possibly encode both a deterministic and non-deterministic automaton is that, we need further conditions to check whether the given data is well-structured to give an output of what we want. The following are some useful utility functions to check whether the given transition table has certain properties:

\begin{code}
-- given data in the format of transitionData, an input state, and input
-- letter, output all possible input/output pairs.
getTrs :: (Eq a, Eq b) => [(a,[(b,a)])] -> a -> b -> [(b,a)]
getTrs allTrs s0 ltr = filter (\x -> fst x == ltr) $ filter (\x -> fst x == s0) allTrs >>= snd

-- utility for checking if a list has duplicates
allUnq:: Eq a => [a] -> Bool
allUnq = unqHelp []
    where
        unqHelp _ [] = True
        unqHelp seen (x:xs) = notElem x seen && unqHelp (x:seen) xs

appendTuple :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
appendTuple (l,l') (m,m') = (l++m,l'++m')
\end{code}

As mentioned, the data type of deterministic automata should be defined as follows:

\begin{code}
data DetAut  l s = DA { states :: [s]
                      , accept :: [s]
                      , delta :: l -> s -> s }
\end{code}

To access a deterministic automaton from an element of \texttt{AutData}, we need to verify that the given transition table is indeed deterministic, i.e. for any current state, for any given input alphabet there exists a unique output state:

\begin{code}
-- check the totality and functionality of the transition table
detCheck :: (Alphabet l, Eq s) => AutData l s -> Bool
detCheck ad = length sts == length (stateData ad) && allUnq sts 
              -- all states are in transitionData exactly once
              && all detCheckHelper stateTrs where              
              -- check transitions for each letter exactly once
  sts = fst <$> transitionData ad
  stateTrs = snd <$> transitionData ad

detCheckHelper :: (Alphabet l, Eq s) => [(Maybe l,s)] -> Bool
detCheckHelper trs = notElem Nothing (fst <$> trs)        
                     -- no empty transitions
                     && alphIter (fromJust . fst <$> trs) 
                     -- transition set is exactly the alphabet

-- contingent on passing safetyCheck, make data into a DA
encodeDA :: (Alphabet l, Eq s) => AutData l s -> Maybe (DetAut l s)
encodeDA d | not $ detCheck d = Nothing
           | otherwise = Just $ DA { states = stateData d
                                   , accept = acceptData d
                                   , delta = safeDelta } where
               safeDelta ltr st = fromJust $ lookup (Just ltr) $ fromJust (lookup st (transitionData d)) 
\end{code}

We end the basic implementation of deterministic automata by providing its semantic layer, i.e. on a given input and an initial state, whether a deterministic automata accept a list of symbols or not. Intuitively, the \texttt{run} function uses the transition function to trasverses an input string on an automaton and output the terminating state. Then \texttt{acceptDA} tests whether the input is accepted by testing whether the terminating state is an accepted state:

\begin{code}
-- takes DA, input letter list, and initial state to output pair
run :: DetAut l s -> s -> [l] -> s
run _ s0 [] = s0
run da s0 (w:ws) = run da (delta da w s0) ws

acceptDA :: (Eq s) => DetAut l s -> s -> [l] -> Bool
acceptDA da s0 w = run da s0 w `elem` accept da
\end{code}

Completely similarly, we implement non-deterministic automata. The only difference now is that the transition function now also accepts empty input, viz. the socalled \emph{$\epsilon$-transitions}, and the result of a transition function is a list of all possible next states.

\begin{code}
data NDetAut l s = NA { nstates :: [s]
                      , naccept :: [s]
                      , ndelta :: Maybe l -> s -> [s] }
\end{code}

Completely similarly, we can encode a non-determinisitic automaton from an element of \texttt{AutData}: {\color{red} Maybe say more.}

\begin{code}
-- make data into an NA (if data formatted properly, go ahead; otherwise, format it then encode)
encodeNA :: (Alphabet l, Eq s) => AutData l s -> NDetAut l s
encodeNA d = NA { nstates = stateData d
                , naccept = acceptData d
                , ndelta = newDelta } where
  newDelta sym st = case lookup st tData of
                      Nothing -> []
                      Just ls -> nub [ st' | (sym', st') <- ls, sym' == sym, isJust sym' || st' /= st ]
  tData = if trsMerged rawTData then rawTData else mergeTrs rawTData
  trsMerged = allUnq . map fst
  rawTData = transitionData d

-- slow, so we don't always want to be calling this
mergeTrs :: Eq s => TDict l s -> TDict l s
mergeTrs [] = []
mergeTrs ((tr0,tr1):trs) = mTr:mergeTrs remTrs where
  mTr = (tr0, fst prop ++ tr1)
  remTrs = snd prop
  prop = propTrs tr0 trs

-- for a given state, propagate all of its output together, and return
-- all of them, as well as the transition data with those removed
-- type TDict l s = [(s, [(Maybe l, s)])]
propTrs :: Eq s => s -> TDict l s -> ([(Maybe l,s)], TDict l s)
propTrs _ [] = ([],[])
propTrs st (tr:trs) = appendTuple resultTuple (propTrs st trs) where
  resultTuple = if st == fst tr then (snd tr,[]) else ([],[tr])
                 
-- put an NA back into autdata, e.g. to turn it into regex
decode :: (Alphabet l, Eq s) => NDetAut l s -> AutData l s
decode nda = AD { stateData = sts
                  , acceptData = naccept nda
                  , transitionData = trandata
                  }
  where sts = nstates nda
        ntrans = ndelta nda
        symlist = Nothing : (Just <$> completeList)
        trandata = graph help sts 
        help st = concatMap (\sym -> (sym,) <$> ntrans sym st) symlist
        graph f as = zip as $ f <$> as
\end{code}

We end with the semantic layer for non-determinisitic automata. The algorithm used for implementing \texttt{runNA} for trasversing an input string on a non-deterministic automaton is inspired by~\cite{web}. Intuitively, we record a list of \emph{active states} at each step of the trasversal, with its corresponding remaining list of inputs. If there are no possible transition states with the given input, we terminiate and record it in the output. The function \texttt{ndautAccept} then checks whether there is an output that consumes all the inputs, and terminiates at an accepting state.

\begin{code}
runNA :: (Alphabet l, Ord s) => NDetAut l s  -> s -> [l] -> [([l], s)]
runNA na st input = 
  case input of
    [] -> ([],) <$> epReachable (ndelta na) st
    (w:ws) -> concatMap (\s -> runNA na s input) nsucc ++
              case wsucc of
                [] -> [(input,st)]
                ls -> concatMap (\s -> runNA na s ws) ls
      where wsucc = ndelta na (Just w) st
    where   nsucc = ndelta na Nothing  st

ndautAccept :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> Bool
ndautAccept na s0 w = any (\(ls,st) -> null ls && st `elem` naccept na) $
                      runNA na s0 w

ndfinalStates :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> [s]
ndfinalStates na s0 w = snd <$> runNA na s0 w
\end{code}

Finally, we implement an algorithm that exhibits the behavioural equivalence between deterministic and non-deterministic automata. The easy direction is that, evidently, any deterministic automaton is also a non-deterministic one, and they evidently accepts the same language:

\begin{code}
-- The trivial forgetful functor: DA -> NA
fromDA :: (Alphabet l) => DetAut l s -> NDetAut l s
fromDA da = NA { nstates = states da
               , naccept = accept da
               , ndelta = newDelta } where
  newDelta Nothing _ = []
  newDelta (Just l) st = [delta da l st]
\end{code}

The non-trivial direction is that any non-deterministic automaton can also be converted into a deterministic one, with possibly different set of states and transition functions. The general idea is simple: We change the set of states to the set of \emph{subset} of the original non-determinisitic automaton. This way, we may code the non-deterministic behaviour in a deterministic way. The algorithm is inspired by~\cite{book_marcelo}.

\begin{code}
-- The Power-set Construction: NA -> DA 
fromNA :: (Alphabet l, Ord s) => NDetAut l s -> DetAut l (Set.Set s)
fromNA nda = DA { states = Set.toList dasts
                , accept = Set.toList $ Set.filter acchelp dasts
                , delta = fromTransNA ntrans
                }
  where ndasts = nstates nda
        dasts  = Set.powerSet $ Set.fromList ndasts
        ndaacc = naccept nda
        acchelp set = not $ Set.disjoint set $ Set.fromList ndaacc
        ntrans = ndelta nda

epReachable :: (Alphabet l, Ord s) => (Maybe l -> s -> [s]) -> s -> [s]
epReachable ntrans st = st : concatMap (epReachable ntrans) 
                                       (ntrans Nothing st)

fromTransNA :: (Alphabet l, Ord s) => (Maybe l -> s -> [s]) -> 
                                      l -> Set.Set s -> Set.Set s
fromTransNA ntrans sym set = result
  where starts = listUnions (epReachable ntrans) set
        step = listUnions (ntrans $ Just sym) starts
        result = listUnions (epReachable ntrans) step
        listUnions f input = Set.unions $ Set.map Set.fromList $ Set.map f input

fromStartNA :: (Alphabet l, Ord s) => NDetAut l s -> s -> Set.Set s
fromStartNA nda st = Set.fromList $ epReachable ntrans st
  where ntrans = ndelta nda
\end{code}

We have tested the behavioural equivalence using the above transition in Section~\ref{sec:Examples}.