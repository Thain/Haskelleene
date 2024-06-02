\subsection{Regular Expressions}\label{sec:Regex}

\begin{code}
module Regex where

import Alphabet ( Alphabet(..) )
\end{code}

In this section, we will define regular expressions, in the Kleene algebraic sense of the term. It's important to note that this version of regular expressions is different from those that are well known to programmers. For example, the language $\{ a^nba^n | n \in \N \}$ is well known to not be regular, and so not have a regular expression that represents it; meanwhile the programmer's regular expressions can encode this language rather easily.

The following serves as our definition of the \textsf{Regex} type. Note the distinction between \texttt{Empty} and \texttt{Epsilon}. The former is the empty language, while the latter is the empty string. Note also the type parameter \texttt{l}. This is so that we can use different input alphabets if we choose; see the \texttt{Alphabet} module for the definition of the \texttt{Alphabet} type class in Section~\ref{sec:Alphabet}.

\begin{code}
data Regex l = Empty | 
               Epsilon |
               L l | 
               Alt (Regex l) (Regex l) |
               Seq (Regex l) (Regex l) |
               Star (Regex l)
  deriving (Eq, Show)
\end{code}
We also write a robust pretty printing function for \texttt{Regex}, with many hard coded cases so as to mimic the conventions of writing regular expressions as best we can. We then also include some quality-of-life functions, sequencing or alternating a list of regexes.
\begin{code}
pPrintRgx :: Alphabet l => Regex l -> String
pPrintRgx Empty = "Em"
pPrintRgx Epsilon = "Ep"
pPrintRgx (L a) = pPrintLetter a
pPrintRgx (Alt (Seq r r') (Seq r'' r''')) = "(" ++ pPrintRgx (Seq r r') ++ ")+("
                                             ++ pPrintRgx (Seq r'' r''') ++ ")"
pPrintRgx (Alt (Seq r r') r'') = "(" ++ pPrintRgx (Seq r r') ++ ")" ++ "+" ++ pPrintRgx r''
pPrintRgx (Alt r'' (Seq r r')) = pPrintRgx r'' ++ "+" ++ "(" ++ pPrintRgx (Seq r r') ++ ")"
pPrintRgx (Alt r r') = pPrintRgx r ++ "+" ++ pPrintRgx r'
pPrintRgx (Seq (Alt r r') (Alt r'' r''')) = "(" ++ pPrintRgx (Alt r r') ++ ")(" 
                                             ++ pPrintRgx (Alt r'' r''') ++ ")"
pPrintRgx (Seq (Alt r r') r'') = "(" ++ pPrintRgx (Alt r r') ++ ")" ++ pPrintRgx r''
pPrintRgx (Seq r'' (Alt r r')) = pPrintRgx r'' ++ "(" ++ pPrintRgx (Alt r r') ++ ")"
pPrintRgx (Seq r (Star (L a))) = pPrintRgx r ++ "(" ++ pPrintLetter a ++ "*)"
pPrintRgx (Seq (Star (L a)) r) = "(" ++ pPrintLetter a ++ "*)" ++ pPrintRgx r
pPrintRgx (Seq r r') = pPrintRgx r ++ pPrintRgx r'
pPrintRgx (Star (L a)) = pPrintLetter a ++ "*"
pPrintRgx (Star r) = "(" ++ pPrintRgx r ++ ")*"

-- QoL functions for sequencing or alternating lists of regexes
seqList, altList :: [Regex l] -> Regex l
seqList = foldr Seq Epsilon
altList = foldr Alt Empty
\end{code}
It is outside of the scope of this project to implement an equivalence checker for regexes. Having said that, there are certain simplifications we can make to regular expressions that will help improve readability and running time. For example:
\begin{align*}
\emptyset + r &= r + \emptyset =  r \\
\epsilon r &= r \epsilon = r
\end{align*}
...and more. The objective here is not to fully simplify the regular expression, but to implement easy simplifications to improve readability and runtime. We loop this function up to a fixed point.
\begin{code}
simplifyRegex :: Eq l => Regex l -> Regex l
simplifyRegex regex | helper regex == regex = regex
                    | otherwise = helper regex where
 helper rx =
  case rx of
    Alt r4 (Seq r1 (Seq (Star r2) r3)) 
      | r1 == r2 && r3 == r4 -> Seq (Star (simplifyRegex r1)) (simplifyRegex r4)
    (Alt Empty r) -> simplifyRegex r
    (Alt r Empty) -> simplifyRegex r
    (Alt r r') | r == r' -> simplifyRegex r
    (Seq r Epsilon) -> simplifyRegex r
    (Seq Epsilon r) -> simplifyRegex r
    (Seq _ Empty) -> Empty
    (Seq Empty _) -> Empty
    (Star Empty) -> Epsilon
    (Star Epsilon) -> Epsilon
    (Star (Star r)) -> simplifyRegex $ Star r
    (Star (Alt r Epsilon)) -> simplifyRegex $ Star r
    (Star (Alt Epsilon r)) -> simplifyRegex $ Star r
    Alt r r' -> Alt (simplifyRegex r) (simplifyRegex r')
    Seq r r' -> Seq (simplifyRegex r) (simplifyRegex r')
    Star r -> Star (simplifyRegex r)
    x -> x
\end{code}
Now we need to set to the task of defining a semantics for these regular expressions. First, we will need a utility function for checking if initial sequences of the word satisfy part of the regex, specifically for the \texttt{Sequence} and \texttt{Star} cases.

This function takes a \texttt{Regex} and a word, and produces all splits of the word where the first part of the split satisfies the regex. For the word $abc$, with the regex $c^\star a^\star$, \texttt{initCheck} would output $(\epsilon, abc)$ and $(a,bc)$. 
\begin{code}
initCheck :: Eq l => Regex l -> [l] -> [([l],[l])]
initCheck r w = filter (regexAccept r . fst) $ splits w where
  splits [] = [([],[])]
  splits (x:xs) = map (appFst x) (splits xs) ++ [([],x:xs)]
  appFst x (y,z) = (x:y,z)
\end{code}
Now we finally define the semantics for our regular expressions. We include special cases for sequencing with a single letter: because our general sequence case will be pretty inefficient, and this is a common use case that is quite fast.

In fact, both our sequencing and star operations are rather slow; this is because we need to examine all initial sequences of the word to see if they can match the regex. This is why \texttt{initCheck} returns the split of the word, rather than just the initial segment that matches: we need to then check the rest of the regex (the other operand in the case of \texttt{Seq}, or the regex again in the case of \texttt{Star}) on what remains of the string.

One potential optimisation we could make to this algorithm: calculate the range of string lengths a regex will accept, and compare this length to the input string, to find easier reject cases. We could pair this with splitting as we go, rather than up front.
\begin{code}
regexAccept :: Eq l => Regex l -> [l] -> Bool
-- the empty language accepts no words
regexAccept Empty _    = False
-- if down to the empty string, only accept the empty word
regexAccept Epsilon [] = True  
regexAccept Epsilon _  = False
-- if down to a single letter, only accept that letter 
regexAccept (L _) []   = False
regexAccept (L l) [c]  = l == c
regexAccept (L _) _ = False
regexAccept (Alt r r') cs = regexAccept r cs || regexAccept r' cs
-- optimisations for simple sequences (one part is just a letter)
regexAccept (Seq (L _) _) [] = False
regexAccept (Seq _ (L _)) [] = False
regexAccept (Seq (L l) r) (c:cs) = l == c && regexAccept r cs 
regexAccept (Seq r (L l)) cs = last cs == l && regexAccept r (init cs)
regexAccept (Seq Epsilon r) cs = regexAccept r cs
regexAccept (Seq r r') cs = any (regexAccept r' . snd) $ initCheck r cs
regexAccept (Star _) [] = True
regexAccept (Star r) cs = 
  any (regexAccept (Star r) . snd) $ ignoreEmpty $ initCheck r cs
  where ignoreEmpty = if regexAccept r [] then init else id 
\end{code}
In the general case of \texttt{Star}, similar to \texttt{Seq}, we want to find all initial segments of the word that satisfy the regular expression; but now we try to proceed using \texttt{Star r} again. There is an important subtlety, however: we want to avoid infinite looping, which may happen if the inner regular expression accepts the empty word.

Take for example the regex $(\epsilon + a)^\star$. This is equivalent to $a^\star$, of course, but introducing these kinds of simplifications to \texttt{simplifyRegex} significantly increases the complexity. If we're not careful, inputting the string $bb$ with this regex will loop infinitely because we will continually find that $(\epsilon,bb)$ satisfies the $\epsilon + a$, and will loop back and forth between \texttt{regexAccept} and \texttt{initCheck} without making any forward progress in matching the word. To avoid this, we check if the inner regex accepts $\epsilon$. If it does, we know it is redundant and we use \texttt{init} to drop the last accepting initial segment: namely $(\epsilon,w)$ for whatever input word $w$.
