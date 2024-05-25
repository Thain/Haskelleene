\section{Regular Expression Library}\label{sec:Regex}

This is where we define the Kleene regular expression structure we will be using throughout the project.

\begin{code}
module Regex where

import Basics -- contains all of our utility functions
import Data.Maybe
-- -----------------
-- REGEX definitions 
-- -----------------

data Regex l = Empty | 
               Epsilon |
               L l | 
               Alt (Regex l) (Regex l) |
               Seq (Regex l) (Regex l) |
               Star (Regex l)
  deriving (Eq)

-- showing a regular expression. Lots of hard-coded cases to make specific nicer and more readable
instance Show l => Show (Regex l) where
  show Empty = "∅"
  show Epsilon = "ɛ"
  show (L a) = show a
  show (Alt (Seq r r') (Seq r'' r''')) = "(" ++ show (Seq r r') ++ ")+(" ++ show (Seq r'' r''') ++ ")"
  show (Alt (Seq r r') r'') = "(" ++ show (Seq r r') ++ ")" ++ "+" ++ show r''
  show (Alt r'' (Seq r r')) = show r'' ++ "+" ++ "(" ++ show (Seq r r') ++ ")"
  show (Alt r r') = show r ++ "+" ++ show r'
  show (Seq (Alt r r') (Alt r'' r''')) = "(" ++ show (Alt r r') ++ ")(" ++ show (Alt r'' r''') ++ ")"
  show (Seq (Alt r r') r'') = "(" ++ show (Alt r r') ++ ")" ++ show r''
  show (Seq r'' (Alt r r')) = show r'' ++ "(" ++ show (Alt r r') ++ ")"
  show (Seq r r') = show r ++ show r'
  show (Star (L a)) = "(" ++ show a ++ "*)"
  show (Star r) = "(" ++ show r ++ ")*"
-- if sticking with altl, seql, then this isn't quite right. need paren cases


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

-- very simple regex simplifications (guaranteed to terminate or your money back)
simplifyRegex :: Eq l => Regex l -> Regex l
simplifyRegex rx = case rx of
                    Alt r4 (Seq r1 (Seq (Star r2) r3)) | r1 == r2 && r3 == r4 -> Seq (Star (simplifyRegex r1)) (simplifyRegex r4)
                    (Alt Empty r) -> simplifyRegex r
                    (Alt r Empty) -> simplifyRegex r
                    (Alt r r') | r == r' -> simplifyRegex r
                    (Seq r Epsilon) -> simplifyRegex r
                    (Seq Epsilon r) -> simplifyRegex r
                    (Seq _ Empty) -> Empty
                    (Seq Empty _) -> Empty
                    (Star Empty) -> Empty
                    (Star Epsilon) -> Epsilon
                    (Star (Star r)) -> simplifyRegex $ Star r
                    (Star (Alt r Epsilon)) -> simplifyRegex $ Star r
                    (Star (Alt Epsilon r)) -> simplifyRegex $ Star r
                    Alt r r' -> Alt (simplifyRegex r) (simplifyRegex r')
                    Seq r r' -> Seq (simplifyRegex r) (simplifyRegex r')
                    Star r -> Star (simplifyRegex r)
                    x -> x

-- (Star (Alt (Alt Epsilon (L a)) (Seq (Alt (L b) (L c)) (Seq (Star (L b)) (Alt (L a) (L c))))),1)

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
-- general Seq case is less efficient
regexAccept (Seq r r') cs = any (regexAccept r' . snd) $ trueInitCheck r cs
-- general Alt case pretty easy
regexAccept (Alt r r') cs = regexAccept r cs || regexAccept r' cs
-- if word is empty, star is true
regexAccept (Star _) [] = True
-- general star case
regexAccept (Star r) cs | regexAccept r [] = any (regexAccept (Star r) . snd) $ initCheck r cs
                        | otherwise = any (regexAccept (Star r) . snd) $ trueInitCheck r cs

-- get all initial sequences of the word that match the regex, except for
-- the empty initial sequence (as this loops forever and goes nowhere)
initCheck :: Eq l => Regex l -> [l] -> [([l],[l])]
initCheck r w = filter (regexAccept r . fst) $ init $ splits w

trueInitCheck :: Eq l => Regex l -> [l] -> [([l],[l])]
trueInitCheck r w = filter (regexAccept r . fst) $ splits w

-- these may eventually be useful so i won't delete them, but they're
-- not getting used right now. --LC

-- what is the maximum length of a string satisfying this regex?
-- Nothing means infinite (in other words, we used a star)
maxLenStr :: Regex l -> Maybe Int
maxLenStr Empty = Just 0
maxLenStr Epsilon = Just 0
maxLenStr (L _) = Just 1
maxLenStr (Alt r r') = maxMaybe (maxLenStr r) (maxLenStr r')
  where maxMaybe x y | isNothing x = x
                     | isNothing y = y
                     | otherwise = max x y
maxLenStr (Seq r r') = sum <$> sequence [maxLenStr r, maxLenStr r']
maxLenStr (Star _) = Nothing

loopSimpRgx :: Eq l => Regex l -> (Regex l,Int)
loopSimpRgx r | simplifyRegex r == r = (r,0)
              | otherwise = (next, count)
  where next = fst loop
        count = 1 + snd loop
        loop = loopSimpRgx (simplifyRegex r)

\end{code}
