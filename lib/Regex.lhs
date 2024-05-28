\subsection{Regular Expression Library}\label{sec:Regex}

\begin{code}
module Regex where
\end{code}

In this section, we will define regular expressions, in the Kleene algebraic sense of the term. It's important to note that this version of regular expressions is different from those that are well known to programmers. For example, the language $\{ a^nba^n | n \in \N \}$ is well known to not be regular, and so not have a regular expression that represents it; meanwhile the programmer's regular expressions can encode this language rather easily.

The following serves as our definition of the \textsf{Regex} type. First we define our base case constructors, \texttt{Empty}, \texttt{Epsilon}, and \texttt{L l}. Note the distinction between \texttt{Empty} and \texttt{Epsilon} type constructors. The former is the regex representing the empty language, that is, the language that has no words in it. The latter represents the empty string, which is the word with no letters, and as a regular expression is the string language containing one string: the empty string.

Note also that we use a type parameter \texttt{l} for this type. This is so that we can use different input alphabets if we so choose; see the \texttt{Alphabet} module for the definition of the \texttt{Alphabet} type class in Section~\ref{sec:Alphabet}.

\begin{code}
data Regex l = Empty | 
               Epsilon |
               L l | 
               Alt (Regex l) (Regex l) |
               Seq (Regex l) (Regex l) |
               Star (Regex l)
  deriving (Eq, Show)
\end{code}
We also write a robust pretty printing function for \texttt{Regex}, with many hard coded cases so as to mimic the conventions of writing regular expressions as we can. We then also include some quality-of-life functions, for example for sequencing or alternating a list of regexes, as well as doing so for some list of input letters. This allows us to turn a word into a regex representing exactly that word quickly and easily.
\begin{code}
pPrintRgx :: Show l => Regex l -> String
pPrintRgx Empty = "em"
pPrintRgx Epsilon = "ep"
pPrintRgx (L a) = show a
pPrintRgx (Alt (Seq r r') (Seq r'' r''')) = "(" ++ pPrintRgx (Seq r r') ++ ")+("
                                             ++ pPrintRgx (Seq r'' r''') ++ ")"
pPrintRgx (Alt (Seq r r') r'') = "(" ++ pPrintRgx (Seq r r') ++ ")" ++ "+" ++ pPrintRgx r''
pPrintRgx (Alt r'' (Seq r r')) = pPrintRgx r'' ++ "+" ++ "(" ++ pPrintRgx (Seq r r') ++ ")"
pPrintRgx (Alt r r') = pPrintRgx r ++ "+" ++ pPrintRgx r'
pPrintRgx (Seq (Alt r r') (Alt r'' r''')) = "(" ++ pPrintRgx (Alt r r') ++ ")(" 
                                             ++ pPrintRgx (Alt r'' r''') ++ ")"
pPrintRgx (Seq (Alt r r') r'') = "(" ++ pPrintRgx (Alt r r') ++ ")" ++ pPrintRgx r''
pPrintRgx (Seq r'' (Alt r r')) = pPrintRgx r'' ++ "(" ++ pPrintRgx (Alt r r') ++ ")"
pPrintRgx (Seq r r') = pPrintRgx r ++ pPrintRgx r'
pPrintRgx (Star (L a)) = "(" ++ show a ++ "*)"
pPrintRgx (Star r) = "(" ++ pPrintRgx r ++ ")*"

-- QoL functions for sequencing or alternating lists of regexes
seqList :: [Regex l] -> Regex l
seqList [l] = l
seqList (l:ls) = Seq l $ seqList ls
seqList [] = Epsilon

altList :: [Regex l] -> Regex l
altList [l] = l
altList (l:ls) = Alt l $ altList ls
altList [] = Empty

-- QoL functions for turning lists of letters into sums or products
seqList', altList' :: [l] -> Regex l
seqList' = seqList . map L
altList' = altList . map L
\end{code}
The proof system for the equational theory of regular expressions, known as Kleene algebra, can reason about equivalence of regular expressions, for example:
\[ a + (b + a^*) = a + (a^\star + b) = (a + a^\star) + b = a^\star + b \]
It is outside of the scope of this project to implement a proof searcher for this system. Having said that, there are certain simplifications we can make to regular expressions that will help improve readability and running time. For example:
\begin{align*}
\emptyset + r &= r + \emptyset =  r \\
\epsilon r &= r \epsilon = r
\end{align*}
...and more. The objective here is not to simplify the regular expression as far as possible, but to implement easy simplifications that improve readability (limiting occurrence of redundancies, and so on).
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
Now we need to set to the task of defining a semantics for these regular expressions. That is, given a list of letters from the input alphabet (a word), check whether it belongs to the language represented by the regular expression. First, we will need a utility function for checking if initial sequences of the word satisfy part of the regex, specifically for the \texttt{Sequence} and \texttt{Star} cases.

This function takes a \texttt{Regex} and a word, and produces all splits of the word where the first part of the split satisfies the regex. By splits of a word, we mean splitting the word into two subwords, that when concatenated give the original word. For example splits of $abc$ are:
\[ [(abc,\epsilon),\ (ab,c),\ (a,bc),\ (\epsilon,abc)] \]
and for this particular input word, with the regex $c^\star a^\star$, \texttt{initCheck} would output $(\epsilon, abc)$ and $(a,bc)$. Note that this function does use \texttt{regexAccept}, which we will define below, and that this function does nothing to reduce the ``size'' of $r$, which means we need to be careful about infinite looping. More on that below.
\begin{code}
initCheck :: Eq l => Regex l -> [l] -> [([l],[l])]
initCheck r w = filter (regexAccept r . fst) $ splits w where
  splits [] = [([],[])]
  splits (x:xs) = map (appFst x) (splits xs) ++ [([],x:xs)]
  appFst x (y,z) = (x:y,z)
\end{code}
Now we finally define the semantics for our regular expressions. Our base cases are simple: the empty language accepts no words, the $\epsilon$ accepts only the empty word, and $l$ for some letter accepts only that letter. We also include special cases for when sequencing with a single letter: because our sequencing checker will be pretty inefficient, and this is a common use case that is quite fast, we encode it directly. The \texttt{Alt} case is also straightforward, effectively just acting as a disjunction in the most simple of terms.

As mentioned above, our sequencing and star operations are slower in general; this is because we need to examine all initial sequences of the word to see if they can match the regex. This is why \texttt{initCheck} returns the split of the word, rather than just the initial segment that matches: we need to then check the rest of the regex (the other operand in the case of \texttt{Seq}, or the regex again in the case of \texttt{Star}) on what remains of the string.

POTENTIAL OPTIMISATION: encode maximal length of a regex and compare to length of the input string, to find easier reject cases. also, don't split up front: do it as we go, this will make longer words accept faster.
\begin{code}
regexAccept :: Eq l => Regex l -> [l] -> Bool
-- the empty language accepts no words
regexAccept Empty _    = False
-- if down to the empty string, only accept the empty word
regexAccept Epsilon [] = True  
regexAccept Epsilon _  = False
-- if down to a single letter, only accept that letter (and if longer, reject too)
regexAccept (L _) []   = False
regexAccept (L l) [c]  = l == c
regexAccept (L _) _ = False
-- optimisations for simple sequences (one part is just a letter)
regexAccept (Seq (L _) _) [] = False
regexAccept (Seq _ (L _)) [] = False
regexAccept (Seq (L l) r) (c:cs) = l == c && regexAccept r cs 
regexAccept (Seq r (L l)) cs = last cs == l && regexAccept r (init cs)
regexAccept (Seq Epsilon r) cs = regexAccept r cs
-- general Alt case pretty easy
regexAccept (Alt r r') cs = regexAccept r cs || regexAccept r' cs
-- general Seq case is less efficient
regexAccept (Seq r r') cs = any (regexAccept r' . snd) $ initCheck r cs
-- if word is empty, star is true
regexAccept (Star _) [] = True
-- general star case
regexAccept (Star r) cs = 
  any (regexAccept (Star r) . snd) $ ignoreEmpty $ initCheck r cs
  where ignoreEmpty = if regexAccept r [] then init else id 
\end{code}
In the general case of \texttt{Star}, similar to \texttt{Seq}, we want to find all initial segments of the word that satisfy the regular expression; but now we try to proceed using \texttt{Star r} again. There is an important, subtlety, however: we want to avoid infinite looping, which may happen if our regular expression accepts the empty word.

Take for example the regex $(\epsilon + a)^\star$. This is equivalent to $a^\star$, of course, but introducing these kinds of simplifications to \texttt{simplifyRegex} significantly increases the complexity. If we're not careful, inputting the string $bbb$ with this regex will loop infinitely because our we will continually find that $(\epsilon,bbb)$ satisfies the regex, and will loop back and forth between \texttt{regexAccept} and \texttt{initCheck} without making any forward progress in matching the word. To avoid this, we check if the inner regex accepts $\epsilon$. If it does, we know that it is redundant (because of our case where \texttt{regexAccept (Star r) [] = True}) and so we use \texttt{init} to drop the last accepting initial segment: given our implementation of \texttt{initCheck}, this will necessarily be $(\epsilon,w)$ for whatever input word $w$.
