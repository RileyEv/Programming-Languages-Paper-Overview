\documentclass[a4paper, twocolumn, 9pt]{extarticle}

% Tiny borders should be default
\usepackage[a4paper, total={7in, 10.25in}]{geometry}

\setlength {\marginparwidth }{2cm}
\usepackage{todonotes}
% Font shit
\usepackage{fontspec}
\usepackage{xunicode}
\usepackage{xcolor}
\defaultfontfeatures{Ligatures=TeX}
\setmainfont[
BoldFont=merriweather-regular.ttf,
ItalicFont=merriweather-light-italic.ttf,
BoldItalicFont=merriweather-bold.ttf
]{merriweather-light.ttf}
\newfontfamily\secfont{merriweather-sans-regular.ttf}
\usepackage{titlesec}
\newcommand{\secstyle}{\secfont\Large\itshape}
\titleformat{\section}%
  {\secstyle} % format
  {\thesection} % label
  {10pt} % sep
  {} % before
  [\normalfont] % after

\newcommand{\subsecstyle}{\secfont\large\itshape}
\titleformat{\subsection}%
  {\subsecstyle} % format
  {\thesubsection} % label
  {10pt} % sep
  {} % before
  [\normalfont] % after

\usepackage{enumitem}
% \usepackage{parskip}
\usepackage{hyphenat}

\usepackage{pgfplots}
\pgfplotsset{compat=newest}
\usepgfplotslibrary{groupplots}
\usepgfplotslibrary{dateplot}

\title{\vspace{-10mm}Advanced Topics in Programming Languages - Paper Overview\vspace{-4mm}}
\author{Riley Evans (re17105)}
\date{\vspace{-3mm}}
 
%include polycode.fmt

\begin{document}
\secfont
\maketitle
\normalfont

%if False

> {-# LANGUAGE KindSignatures, GADTs, RankNTypes, LambdaCase #-}
> import Prelude hiding (or)

%endif


\section{DSLs}

A Domain Specific Language (DSL) is a programming language that has a specialised domain or use-case. This differs from a General Purpose Language (GPL), which can be applied across a larger set of domains. DSLs can be split into two different categories: standalone and embedded. Standalone DSLs require their own compiler and typically have their own syntax. Embedded DSLs use a GPL as a host language, therefore they use the syntax and compiler from that GPL. This means that they are easier to maintain and are often quicker to develop than standalone DSLs.

An embedded DSL can be implemented with two main techniques. Firstly, a deep approach can be taken, this means that terms in the DSL will construct an Abstract Syntax Tree (AST). This can then be used to apply optimisations and then evaluated. A second approach is to define the terms as their semantics, avoiding the AST. This approach is referred to as a shallow embedding.


\section{Parsers}
In the paper, a circuit language used to describe the different techniques for folding DSLs. For the purposes of this review a new DSL will be introduced - this is a parser DSL. This langauge is made up of 6 terms, they provide all the essential operations needed in a parser.

%if False

> type Parser a = Int

%endif

> empty    ::                                  Parser a
> pure     :: a ->                             Parser a
> satisfy  :: (Char -> Bool) ->                Parser Char
> try      :: Parser a ->                      Parser a
> ap       :: Parser (a -> b) ->  Parser a ->  Parser b
> or       :: Parser a ->         Parser a ->  Parser a

For example, a parser that can parse a or b can be defined as,

> aorb :: Parser Char
> aorb = (satisfy (=='a')) `or` (satisfy (== 'b'))


A deep embedding of this parser language is defined as \textit{Parser2} in the appendix. A function \textit{size} can be defined that finds the size of the AST created in the deep embedding.

> type Size = Int
> size :: Parser2 a -> Size
> size  (Empty2)      =  1
> size  (Pure2 _)     =  1
> size  (Satisfy2 _)  =  1
> size  (Try2 px)     =  1 +  size px
> size  (Ap2 pf px)   =  1 +  size pf  + size px
> size  (Or2 px py)   =  1 +  size px  + size py


TODO: everything below this



It is clear that size is a fold over Parser2, hence it is a suitable semantics for a shallow embedding.


> type Parser3 a = Int
> pure3 _ = 1
> satisfy3 _ = 1
> empty3 = 1
> try3 px = px + 1
> ap3 pf px = pf + pf + 1
> or3 px py = px + py + 1
>
> size3 :: Parser3 a -> Size
> size3 = id


\section{Folds}

Blah blah

The shape is able to be captured in an instance of the Functor type class.
In a difference to the paper Parsers are a typed DSL. Therefore, we need to define an instance of the IFunctor type class,
in order to retain these types. TODO: Type indices

> class IFunctor f where
>   imap :: (forall i . a i -> b i) -> f a i -> f b i

> data ParserF (k :: * -> *) (a :: *) where
>   PureF    :: a -> ParserF k a
>   SatisfyF :: (Char -> Bool) -> ParserF k Char
>   EmptyF   :: ParserF k a
>   TryF     :: k a -> ParserF k a
>   ApF :: k (a -> b) -> k a -> ParserF k b
>   OrF :: k a -> k a -> ParserF k a

> instance IFunctor ParserF where
>   imap _ EmptyF = EmptyF
>   imap _ (SatisfyF c) = SatisfyF c
>   imap _ (PureF x) = PureF x
>   imap f (TryF px) = TryF (f px)
>   imap f (ApF pf px) = ApF (f pf) (f px)
>   imap f (OrF px py) = OrF (f px) (f py)


The paper here attempts to hide its usage of Fix and cata by specifying specialised versions of them for Circuit4.
Instead, we can just use Fix and cata for clarity.

> newtype Fix f a = In (f (Fix f) a)
> type Parser4 a = Fix ParserF a

> cata :: IFunctor f => (forall i . f a i -> a i) -> Fix f i -> a i
> cata alg (In x) = alg (imap (cata alg) x)



Now we have all the building blocks needed to start folding our parser DSL.
Size can be defined as a fold, which can be determined by the sizeAlg

> newtype Const a i = Const a
> unConst :: Const a i -> a
> unConst (Const x) = x

> sizeAlg :: ParserF (Const Size) a -> Const Size a
> sizeAlg (PureF _) = Const 1
> sizeAlg (SatisfyF _) = Const 1
> sizeAlg EmptyF = Const 1
> sizeAlg (TryF (Const n)) = Const (n + 1)
> sizeAlg (ApF (Const pf) (Const px)) = Const (pf + px + 1)
> sizeAlg (OrF (Const px) (Const py)) = Const (px + py + 1)

> size4 :: Parser4 a -> Size
> size4 = unConst . cata sizeAlg


\section{Multi}


A common thing with DSLs is to evaluate multiple interpretations.
For example, a parser may also want to know the maximum characters it will read.
In a deep embedding this is simple, we just provide a second algebra.

> type MaxMunch = Int
>
> maxMunchAlg :: ParserF (Const MaxMunch) a -> Const MaxMunch a
> maxMunchAlg (PureF _)                   = Const 0
> maxMunchAlg  EmptyF                     = Const 0
> maxMunchAlg (SatisfyF c)                = Const 1
> maxMunchAlg (TryF (Const px))           = Const px
> maxMunchAlg (ApF (Const pf) (Const px)) = Const (pf + px)
> maxMunchAlg (OrF (Const px) (Const py)) = Const (max px py)

> maxMunch4 :: Parser4 a -> MaxMunch
> maxMunch4 = unConst . cata maxMunchAlg

But what about a shallow embedding? So far we have only seen parsers be able to have single semantics,
so how could we calculate both the maxMunch and size of a parser? It turns out the solution is simple,
we can use a pair and calculate both interpretations simulataneously.

> type Parser5 = (Size, MaxMunch)

> size5 :: Parser5 -> Size
> size5 = fst

> maxMunch5 :: Parser5 -> Size
> maxMunch5 = snd

> sizeMaxMunchAlg :: ParserF (Const (Size, MaxMunch)) a -> Const (Size, MaxMunch) a
> sizeMaxMunchAlg (PureF _)                                = Const (1,          0)
> sizeMaxMunchAlg  EmptyF                                  = Const (1,          0)
> sizeMaxMunchAlg (SatisfyF c)                             = Const (1,          1)
> sizeMaxMunchAlg (TryF (Const (s, mm)))                   = Const (s + 1,      mm)
> sizeMaxMunchAlg (ApF  (Const (s, mm)) (Const (s', mm'))) = Const (s + s' + 1, mm + mm')
> sizeMaxMunchAlg (OrF  (Const (s, mm)) (Const (s', mm'))) = Const (s + s' + 1, max mm mm')


Although this is an algebra, you are able to glean the shallow embedding from this, for example:

> ap5 pf px = sizeMaxMunchAlg (ApF pf px)


\section{dependent}

zygomorphisms

TODO: something in parsley. \cite{10.1145/3409002}

% https://github.com/J-mie6/ParsleyHaskell/blob/abe5df58cca05d8825036790f9c138183fe852b1/Parsley/Frontend/CombinatorAnalyser.hs#L70


\section{Context Sensitive}


Parsers themselves inherently require context sensitive interpretations - what you can parse will
decide what you are able to parse in latter points of the parser.

Using the semantics from https://github.com/zenzike/yoda we are able to implement a simple parser using an accumulating fold.


> newtype Yoda a = Yoda {unYoda :: String -> [(a, String)]}

-- > newtype Yoda a = Yoda (String -> [(a, String)])
-- > unYoda :: Yoda a -> (String -> [(a, String)])
-- > unYoda (Yoda px) = px


> yodaAlg :: ParserF Yoda a -> Yoda a
> yodaAlg (PureF x) = Yoda (\ts -> [(x, ts)])
> yodaAlg  EmptyF   = Yoda (const [])
> yodaAlg (SatisfyF c) = Yoda (\case
>   []     -> []
>   (t:ts') -> [(t, ts') | c t])
> yodaAlg (TryF px) = px
> yodaAlg (ApF (Yoda pf) (Yoda px)) = Yoda (\ts -> [(f x, ts'') | (f, ts')  <- pf ts
>                                                               , (x, ts'') <- px ts'])
> yodaAlg (OrF (Yoda px) (Yoda py)) = Yoda (\ts -> px ts ++ py ts)


> parse :: Parser4 a -> (String -> [(a, String)])
> parse = unYoda . cata yodaAlg


> newtype Parsec a = Parsec (String -> [String]) -- not correct


\section{Parameterized}

Previously we saw how to add multiple types of interpretations to a shallow embedding. We used pairs to allow us to have two interpretations.
However, this doesn't extend very well to many more interpretations. Language support starts to fade for larger tuples and it will begin to become messy.

We already know that shallow embeddings are folds, so we could create a shallow embedding that is in terms of a single parameterized interterpretation.


> newtype Parser7 i = P7 {unP7 :: forall a . ( forall j . ParserF a j -> a j) -> a i}
>
> pure7 :: i -> Parser7 i
> pure7 x = P7 (\h -> h (PureF x))
> empty7 :: Parser7 a
> empty7 = P7 (\h -> h EmptyF)
> satisfy7 c = P7 (\h -> h (SatisfyF c))
> try7 :: Parser7 a -> Parser7 a
> try7 px = P7 (\h -> h (TryF (unP7 px h)))
> ap7 :: Parser7 (a -> b) -> Parser7 a -> Parser7 b
> ap7 pf px = P7 (\h -> h (ApF (unP7 pf h) (unP7 px h)))
> or7 px py = P7 (\h -> h (OrF (unP7 px h) (unP7 py h)))


\section{Implicitly Parameterized}


TODO





> main :: IO ()
> main = undefined

\bibliography{biblo}


\section{Appendix}

> data Parser_2 :: * -> * where
>   Pure_2 :: a -> Parser_2 a
>   Satisfy_2 :: (Char -> Bool) -> Parser_2 Char
>   Empty_2 :: Parser_2 a
>   Try_2 :: Parser_2 a -> Parser_2 a
>   Ap_2 :: Parser_2 (a -> b) -> Parser_2 a -> Parser_2 b
>   Or_2 :: Parser_2 a -> Parser_2 a -> Parser_2 a

\end{document}
