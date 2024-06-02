
\subsection{Deterministic and Non-Deterministic Automata}\label{sec:Automata}

Our first major goal is to implement (non)deterministic automata. Recall that an automaton with input alphabet $\Sigma$ consists of a set of states, a subset of accepting states, and a transition function $\delta$. As input, $\delta$ takes a symbol of the alphabet, and a current state of the automaton. For a deterministic automaton, it outputs a unique next state; For a non-deterministic automaton, it outputs a \emph{list} of possible next states.

\begin{code}
{-# LANGUAGE TupleSections #-}

module Automata where

import Alphabet ( Alphabet(..), alphIter ) -- contains all of our utility functions
import Data.Maybe ( isJust, fromJust, isNothing )
import Data.List ( nub, intersect )
import qualified Data.Set as Set
\end{code}

However, since $\delta$ of an automaton is a \emph{function}, it is not directly definable as inputs. Our implementation choice is to record the \emph{transition table} of the transition function, and use the following types as an interface of encoding and decoding an automata with finite inputs:

\begin{code}
type TDict l s = [(s, [(Maybe l, s)])]

data AutData l s = AD { stateData :: [s] 
                      , acceptData :: [s] 
                      , transitionData :: TDict l s }

pPrintAD :: (Alphabet l, Show s, Eq l, Eq s) => AutData l s -> String
pPrintAD ad = unlines $ ["States:" ++ showSts ad (stateData ad),"","Transitions:"]
                         ++ (concatMap transitions . transitionData) ad where
    showSts d = foldr (\s l -> " " ++ show s ++ isAccept s d ++ l) ""
    isAccept s d = if s `elem` acceptData d then "*" else ""
    transitions (s,trs) = map (stTrs s) trs
    stTrs s t = show s ++ " --" ++ letter ++ "> " ++ output where
      letter | isNothing (fst t) = "Em"
             | otherwise = (pPrintLetter . fromJust . fst) t ++ "-"
      output = show $ snd t
\end{code}

Here \texttt{l} should be thought of as the type of the chosen alphabet, while \texttt{s} is the type of our states. The type \texttt{TDict} then acts as the type of transition tables. A pair in \texttt{TDict} should be thought of recoding the information of given a current state, what are the possible output states of a given input. The fact that we have used \texttt{Maybe l} is that we want the type \texttt{AutData} to be simultaneously able to record both deterministic and non-deterministic automata, thus with the possibility of $\epsilon$-transitions. For some examples of using \texttt{AutData} to encode automata, see Section~\ref{subsec:Examples}.

As mentioned, the data type of deterministic automata should be defined as follows:

\begin{code}
data DetAut  l s = DA { states :: [s]
                      , accept :: [s]
                      , delta :: l -> s -> s }
\end{code}

A consequence of using the same data type (\texttt{AutData}) to encode both deterministic and non-deterministic automata is that we need to check whether the data defines a deterministic automaton. The following are some useful utility functions to check whether the given transition table has certain properties:

\begin{code}
-- intended to be used as aut `trsOf` s, to see what transitions s has in aut
trsOf :: Eq s => AutData l s -> s -> [(Maybe l, s)]
trsOf aut s 
  | isNothing $ lookup s $ transitionData aut = []
  | otherwise = fromJust $ lookup s $ transitionData aut

-- "all unique"
allUnq:: Eq a => [a] -> Bool
allUnq = unqHelp [] where
   unqHelp _ [] = True
   unqHelp seen (x:xs) = notElem x seen && unqHelp (x:seen) xs

appendTuple :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
appendTuple (l,l') (m,m') = (l++m,l'++m')
\end{code}

Now we can encode \texttt{AutData} as a deterministic automaton, so long as the data it describes \emph{can} do so:

\begin{code}
-- contingent on passing detCheck, turn data into DA
encodeDA :: (Alphabet l, Eq s) => AutData l s -> Maybe (DetAut l s)
encodeDA d | not $ detCheck d = Nothing
           | otherwise = Just $ DA { states = stateData d
                                   , accept = acceptData d
                                   , delta = safeDelta } where
    tData = transitionData d
    safeDelta ltr st = (fromJust . lookup (Just ltr) . fromJust . lookup st) tData      -- convert data to delta functionp
    detCheck ad = length (fst <$> tData) == length (stateData ad) && allUnq (fst <$> tData) -- all states are in transitionData exactly once
               && all (detCheckTr . snd) tData
    detCheckTr trs = notElem Nothing (fst <$> trs)        -- no empty transitions
                     && alphIter (fromJust . fst <$> trs) -- transition set is exactly the alphabet
\end{code}

We end the basic implementation of deterministic automata by providing its semantic layer, i.e. on a given input and an initial state, whether a deterministic automata accept a list of symbols or not. Intuitively, the \texttt{run} function uses the transition function to trasverses an input string on an automaton and output the terminating state. Then \texttt{acceptDA} tests whether the input is accepted by testing whether the terminating state is an accepted state:

\begin{code}
run :: DetAut l s -> s -> [l] -> s
run _ s0 [] = s0
run da s0 (w:ws) = run da (delta da w s0) ws

acceptDA :: (Eq s) => DetAut l s -> s -> [l] -> Bool
acceptDA da s0 w = run da s0 w `elem` accept da
\end{code}

We now proceed to implement non-deterministic automata, in a very similar way. The only difference is that the transition function now also accepts empty input, viz. the so-called \emph{$\epsilon$-transitions}, and the result of a transition function is a list of all possible next states.

\begin{code}
data NDetAut l s = NA { nstates :: [s]
                      , naccept :: [s]
                      , ndelta :: Maybe l -> s -> [s] }

-- all DAs are also NAs: the trivial forgetful functor DA -> NA
fromDA :: (Alphabet l) => DetAut l s -> NDetAut l s
fromDA da = NA { nstates = states da
               , naccept = accept da
               , ndelta = newDelta } where
  newDelta Nothing _ = []
  newDelta (Just l) st = [delta da l st]
\end{code}

It will be convenient for us to be able to convert \texttt{NDetAut}s back into \texttt{AutData}, as in some contexts working with the explicit data is easier, for example Kleene's algorithm (covered in Section~\ref{sec:Kleene}).

\begin{code}
decode :: (Alphabet l, Eq s) => NDetAut l s -> AutData l s
decode nda = AD { stateData = sts
                  , acceptData = naccept nda
                  , transitionData = trandata }
  where sts = nstates nda
        ntrans = ndelta nda
        symlist = Nothing : (Just <$> completeList)
        trandata = graph help sts 
        help st = concatMap (\sym -> (sym,) <$> ntrans sym st) symlist
        graph f as = zip as $ f <$> as
\end{code}

As an aside, we can now actually pretty print both \texttt{DetAut} and \texttt{NDetAut}, by decoding them to \texttt{AutData} and using the pretty print function we defined for that:

\begin{code}
pPrintNA :: (Alphabet l, Show s, Eq l, Eq s) => NDetAut l s -> String
pPrintNA = pPrintAD . decode

pPrintDA :: (Alphabet l, Show s, Eq l, Eq s) => DetAut l s -> String
pPrintDA = pPrintAD . decode . fromDA
\end{code}

Now we can encode NAs from \texttt{AutData}, and there's no need to fear the data being invalid; though we will want to reformat the data if it's not organised properly, for example listing the potential transitions from a state split into different parts of the \texttt{TDict}. We also ignore $\epsilon$ loops, as they do not alter the behaviour of the automaton and create unnecessary complexities for the semantic algorithm.
 
\begin{code}
-- make data into an NA (if data formatted properly; otherwise, format then encode)
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
  mergeTrs [] = []
  mergeTrs ((tr0,tr1):trs) = mTr:mergeTrs remTrs where
    mTr = (tr0, fst prop ++ tr1)
    remTrs = snd prop
    prop = propTrs tr0 trs
  -- for a given state, propagate all of its outputs together
  propTrs _ [] = ([],[])
  propTrs st (tr:trs) = appendTuple resultTuple (propTrs st trs) where
    resultTuple = if st == fst tr then (snd tr,[]) else ([],[tr])
\end{code}                

Now we implement the semantic layer for non-deterministic automata. The algorithm used for implementing \texttt{runNA} for traversing an input string on a non-deterministic automaton is inspired by~\cite{web}. We keep a set of \emph{active states}, along with what is left of the word in their trace. We use \texttt{oneStep} to simulate traversing an arrow in the automaton. We run, one step at a time, updating our set of active states, and stopping when we reached a fixed point.

\begin{code}
runNA :: (Alphabet l, Ord s) => NDetAut l s  -> s -> [l] -> [([l], s)]
runNA na st w = (Set.elems . runNAFixPt na . Set.map (w,)) start
  where start = if null w then Set.singleton st else Set.fromList $ map snd $ runNA na st []
        runNAFixPt nda active = if active == next then active else runNAFixPt na next
          where next = appStep active
                appStep ac = Set.fromList $ concatMap (uncurry oneStep) ac
                oneStep [] s = ([], st) : (([],) <$> ndelta nda Nothing s)
                oneStep (c:cs) s  = ((cs,) <$> ndelta nda (Just c) s)
                                        ++ ((c:cs,) <$> epReachable nda s)

epReachable :: (Alphabet l, Ord s) => NDetAut l s -> s -> [s]
epReachable na s = map snd (runNA na s [])

acceptNA :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> Bool
acceptNA na s0 w = any (\(ls,st) -> null ls && st `elem` naccept na) $ runNA na s0 w

ndfinalStates :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> [s]
ndfinalStates na s0 w = snd <$> runNA na s0 w
\end{code}

Finally, we implement algorithms to exhibit the behavioural equivalence between deterministic and non-deterministic automata. As discussed above, all DAs are of course NAs; but for every NA, we can also construct an DA with equivalent behaviours. The general idea is simple: We change the set of states to the set of \emph{subsets} of the original non-determinisitic automaton. This way, we may code the non-deterministic behaviour in a deterministic way. The algorithm is inspired by~\cite{book_marcelo}. 

\begin{code}
fromNA :: (Alphabet l, Ord s) => NDetAut l s -> DetAut l (Set.Set s)
fromNA nda = DA { states = Set.toList subsets
                , accept = Set.toList $ Set.filter acchelp subsets
                , delta = psetDelta }
  where subsets  = Set.powerSet $ Set.fromList $ nstates nda
        acchelp set = (not . Set.disjoint set . Set.fromList) acceptSingles
        acceptSingles = filter (\s -> (not . null) (epReachable nda s `intersect` naccept nda)) (nstates nda)
        psetDelta l s = Set.unions $ Set.map (onestep l) s
        onestep l s = Set.fromList $ result ++ concatMap (epReachable nda) result
          where result = ndelta nda (Just l) s

-- determinise NA, then run as as DA and check acceptance
dtdAccept :: (Alphabet l, Ord s) => NDetAut l s -> s -> [l] -> Bool
dtdAccept na st w = run dtd initSt w `elem` accept dtd
   where dtd = fromNA na
         initSt = Set.fromList (epReachable na st)
\end{code}
We test the claimed behavioural equivalence in Section~\ref{sec:Testing}.
