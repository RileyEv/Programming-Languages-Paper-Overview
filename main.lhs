%TC:envir hscode [] ignore
%options ghci -XTypeOperators
\documentclass[a4paper, twocolumn, 10pt]{extarticle}

% Tiny borders should be default
\usepackage[a4paper, total={7in, 10.25in}]{geometry}

\setlength {\marginparwidth }{2cm}
\usepackage{todonotes}
% Font shit
%\usepackage{fontspec}
%\usepackage{xunicode}
%\usepackage{xcolor}

\usepackage{libertine}
\usepackage{url}
\newmuskip\codemuskip
\codemuskip=4.0mu plus 2.0mu minus 2.0mu\relax
\newcommand\codeskip{\mskip\codemuskip}%
\let\codefont\textsf
\newcommand\sub[1]{\ensuremath{_{\text{#1}}}}

\usepackage{xspace}
\newcommand\keyw[1]{{\codefont{\textbf{#1}}}}
\newcommand\id[1]{\Varid{#1}}
\newcommand\idsym[1]{\mathbin{\id{#1}}}
\newcommand{\vertrule}[1][1.0ex]{\rule[-0.0ex]{.45pt}{#1}}

\usepackage[sort, numbers]{natbib}
\bibliographystyle{ACM-Reference-Format}
\defcitealias{embedding}{\textit{Folding Domain-Specific Languages: Deep and Shallow Embeddings}}

\usepackage{enumitem}
\usepackage{hyphenat}
\usepackage[switch]{lineno}
%\linenumbers


\title{\vspace{-10mm}An Overview of \citetalias{embedding}\vspace{-4mm}}
\author{Riley Evans (re17105)}
\date{\vspace{-3mm}}


%include polycode.fmt
%include forall.fmt

%format `comp_` = "\cdot "
%subst space        = "\codeskip "
%subst char a       = "\text{\ttfamily{\textquotesingle}" a "\textquotesingle}"
%subst backquoted a = "\mathbin{\text{\`{}}" a "\text{\`{}}}"

\renewcommand\Varid[1]{\codefont{#1}}
\let\Conid\Varid
%format return = "\keyw{return}"

\begin{document}
\maketitle

%if False

> {-# LANGUAGE  KindSignatures, GADTs, RankNTypes, LambdaCase, FlexibleInstances,
>               GeneralizedNewtypeDeriving, TypeOperators, MultiParamTypeClasses,
>               FlexibleContexts #-}
> import Prelude hiding (or)
> import Data.Coerce (coerce)

%endif

\section{Introduction}

This is an overview of the techniques described in the paper \citetalias{embedding}.
The paper demonstrates a series of techniques that can be used when folding Domain Specific Languges.
It does so through the use of a simple parallel prefix circuit language~\cite{scans}.


In this overview a small parser combinator language will be used.
This language brings one key feature that was not described in the paper: how to apply these techniques to a typed language.
Only a minimal functionally complete set of combinators have been included in the language to keep it simple.
However, all other combinators usually found in a combinator language can be contructed from this set.


%% The paper takes an example Domain Specific Language and then demonstrates a series of techniques that are helpful for folding them.





%% What is the paper? What are its core ideas?

%% How will the techniques be demoed? Pros/Cons of why they are useful for the parsing language.


\section{Background}

\subsection{DSLs}

A Domain Specific Language (DSL) is a programming language that has a specialised domain or use-case.
This differs from a General Purpose Language (GPL), which can be applied across a larger set of domains.
DSLs can be split into two different categories: standalone and embedded. Standalone DSLs require their own compiler and typically have their own syntax.
Embedded DSLs use a GPL as a host language, therefore they use the syntax and compiler from that GPL.
This means that they are easier to maintain and are often quicker to develop than standalone DSLs.

An embedded DSL can be implemented with two main techniques.
Firstly, a deep approach can be taken, this means that terms in the DSL will construct an Abstract Syntax Tree (AST) as a host language datatype.
This can then be used to apply optimisations and then evaluated.
A second approach is to define the terms as first class components of the language, avoiding the creation of an AST - this is known as a shallow embedding.


\subsection{Parsers}

A parser is a used to convert a series of tokens into another language.
For example converting a string into a Haskell datatype.
Parser combinators provide a flexible approach to constructing parsers.
Unlike parser generators, a combinator library is embedded within a host language: using combinators to construct the grammar.
This makes it a suitable to demonstrate the techniques descriped in this paper for folding the DSL to create parsers.

The langauge is made up of 6 terms, they provide all the essential operations needed in a parser.

%if False

> type Parser a = Int

%endif

> empty    :: Parser a
> pure     :: a                ->  Parser a
> satisfy  :: (Char -> Bool)   ->  Parser Char
> try      :: Parser a         ->  Parser a
> ap       :: Parser (a -> b)  ->  Parser a  ->  Parser b
> or       :: Parser a         ->  Parser a  ->  Parser a

%if False

> empty = undefined
> pure = undefined
> satisfy = undefined
> try = undefined
> ap = undefined
> or = undefined

%endif


For example, a parser that can parse the characters |'a'| or |'b'| can be defined as,

> aorb :: Parser Char
> aorb = satisfy (== 'a') `or` satisfy (== 'b')


A deep embedding of this parser language is defined in the alegebraic datatype:

%format Parser2
%format Empty2
%format Pure2
%format Satisfy2
%format Try2
%format Ap2
%format Or2

> data Parser2 (a :: *) where
>   Empty2    ::  Parser2 a
>   Pure2     ::  a                 ->  Parser2 a
>   Satisfy2  ::  (Char -> Bool)    ->  Parser2 Char
>   Try2      ::  Parser2 a         ->  Parser2 a
>   Ap2       ::  Parser2 (a -> b)  ->  Parser2 a  ->  Parser2 b
>   Or2       ::  Parser2 a         ->  Parser2 a  ->  Parser2 a


This can be interpretted by defining a function such as |size|, that finds the size of the AST used to construct the parser - this can be found in the appendix.
|size| interprets the deep embedding, by folding over the datatype.
See the appendix for how to add an interpretation with a shallow embedding.


\section{Folds}

It is possible to capture the shape of an abstract datatype through the |Functor| type class.
It is possible to capture the shape of an abstract datatype as a |Functor|.
The use of a |Functor| allows for the specification of where a datatype recurses.
There is however one problem, a functor expresing the parser language is required to be typed.
Parsers require the type of the tokens being parsed.
For example a parser reading tokens that make up an expression could have the type |Parser Expr|.
A functor does not retain the type of the parser, therefore it is required to define a special type class called |IFunctor|, which is able to maintain the type indicies~\cite{mcbride2011functional}.
A full definition can be found in the appendix.

The shape of |Parser2|, can be seen in |ParserF| where the |k a| marks the recursive spots.


> data ParserF (k :: * -> *) (a :: *) where
>   EmptyF   :: ParserF k a
>   PureF    :: a               -> ParserF k a
>   SatisfyF :: (Char -> Bool)  -> ParserF k Char
>   TryF     :: k a             -> ParserF k a
>   ApF      :: k (a -> b)      -> k a   -> ParserF k b
>   OrF      :: k a             -> k a   -> ParserF k a

> instance IFunctor ParserF where
>   imap _ EmptyF        = EmptyF
>   imap _ (PureF x)     = PureF     x
>   imap _ (SatisfyF c)  = SatisfyF  c
>   imap f (TryF px)     = TryF  (f px)
>   imap f (ApF pf px)   = ApF   (f pf)  (f px)
>   imap f (OrF px py)   = OrF   (f px)  (f py)

%format Parser4

|Fix| is used to get the fixed point of the functor.
It contains the structure needed to make the datatype recursive.
|Parser4| is the fixed point of |ParserF|.

> type Parser4 a = Fix ParserF a

A mechanism is now required for folding this abstract datatype.
This is possible through the use of a catamorphism, which is a generalised way of folding an abstract datatype.
Therefore, the |cata| function can be used - a definition can be found in the appendix.


Now all the building blocks have been defined that allow for the folding of the parser DSL.
|size| can be defined as a fold, which is determined by the |sizeAlg|.
Due to parsers being a typed language, a constant functor is required to preserve the type indicies.

%format size4

> type ParserAlg a i = ParserF a i -> a i
>
> newtype C a i = C { unConst :: a}
>
> sizeAlg :: ParserAlg (C Size) i
> sizeAlg EmptyF         = C 1
> sizeAlg (PureF     _)  = C 1
> sizeAlg (SatisfyF  _)  = C 1
> sizeAlg (TryF (C n))   = C $ n + 1
> sizeAlg (ApF (C pf) (C px)) = C $ pf + px + 1
> sizeAlg (OrF (C px) (C py)) = C $ px + py + 1
>
> size4 :: Parser4 a -> Size
> size4 = unConst . cata sizeAlg


\subsection{Multiple Interpretations}

In DSLs it is common to want to evaluate multiple interpretations.
For example, a parser may also want to know the maximum characters it will read (maximum munch).
In a deep embedding this is simple, a second algebra can be defined.

%format maxMunch4

> type MM = Int
>
> mmAlg :: ParserAlg (C MM) i
> mmAlg (PureF _)           = C 0
> mmAlg  EmptyF             = C 0
> mmAlg (SatisfyF c)        = C 1
> mmAlg (TryF (C px))       = C px
> mmAlg (ApF (C pf) (C px)) = C $ pf + px
> mmAlg (OrF (C px) (C py)) = C $ max px py
>
> maxMunch4 :: Parser4 a -> MM
> maxMunch4 = unConst . cata mmAlg

However, in a shallow embedding it is not as easy.
To be able to evaluate both semantics a pair can be used, with both interpretations being evaluated simultaneously.
If many semantics are required this can become cumbersome to define.

%format Parser5
%format size5
%format maxMunch5
%format s'

> type Parser5 = (Size, MM)
>
> size5 :: Parser5 -> Size
> size5 = fst
>
> maxMunch5 :: Parser5 -> Size
> maxMunch5 = snd
>
> smmAlg :: ParserAlg (C (Size, MM)) a
> smmAlg (PureF _)           = C (1,      0)
> smmAlg EmptyF              = C (1,      0)
> smmAlg (SatisfyF c)        = C (1,      1)
> smmAlg (TryF (C (s, mm)))  = C (s + 1,  mm)
> smmAlg (ApF  (C (s, mm)) (C (s', mm')))
>   = C (s + s' + 1, mm + mm')
> smmAlg (OrF  (C (s, mm)) (C (s', mm')))
>   = C (s + s' + 1, max mm mm')


Although this is an algebra, you are able to learn the shallow embedding from this, for example:

%format ap5
%format or5

> ap5 pf px = smmAlg (ApF pf px)
> or5 px py = smmAlg (OrF px py)


\subsection{Dependent Interpretations}

In a more complex parser combinator library that perform optimisations on a deep embedding,
it could also be possible that there is a primary fold that depends on other secondary folds on parts of the AST.
Folds such as this are named mutumorphisms~\cite{Fokkinga1989TuplingAM},
they can be implemented by tupling the functions in the fold.
\citet{parsley} makes use of a zygomorphism -
a special case where the dependency is only one-way - to perform consumption analysis.


\subsection{Context-sensitive Interpretations}


Parsers themselves inherently require context sensitive interpretations - what can be parsed will
depend on what has previously been parsed.

Using the semantics from~\citet{wuYoda}, an implementation can be given for a simple parser using an accumulating fold.

%format ts'
%format ts''

> newtype Y a = Y {unYoda :: String -> [(a, String)]}


> yAlg :: ParserAlg Y i
> yAlg (PureF x)     = Y $ \ts -> [(x, ts)]
> yAlg  EmptyF       = Y $ const []
> yAlg (SatisfyF c)  = Y $ \ case
>   []       -> []
>   (t:ts')  -> [(t, ts') | c t]
> yAlg (TryF px)     = px
> yAlg (ApF (Y pf) (Y px)) = Y $ \ts ->
>   [(f x, ts'')  |   (f,  ts')   <- pf ts
>                 ,   (x,  ts'')  <- px ts']
> yAlg (OrF (Y px) (Y py)) = Y $ \ts -> px ts ++ py ts
>
> parse :: Parser4 a -> (String -> [(a, String)])
> parse = unYoda . cata yAlg


\subsection{Parameterized Interpretations}

%format Parser7
%format pure7
%format empty7
%format satisfy7
%format try7
%format ap7
%format or7
%format P7
%format unP7

Previously, when defining multiple interpretations in a shallow embedding, a tuple was used.
However, this does not extend well when many interpretations are needed.
Large tuples tend to lack good language support and will become messy to work with.
It would be beneficial if a shallow embedding could have a parameter that gives it the interpretation.

|Parser7| allows for this approach,
the shallow embedding is made up of first class functions that require an algebra argument.
This algebra describes how the shallow embedding should fold the structure.


> newtype Parser7 i = P7
>   {unP7 :: forall a . ( forall j . ParserF a j -> a j) -> a i}
>
> pure7 :: a -> Parser7 a
> pure7 x = P7 (\h -> h (PureF x))
>
> empty7 :: Parser7 a
> empty7 = P7 (\h -> h EmptyF)
>
> satisfy7 :: (Char -> Bool) -> Parser7 Char
> satisfy7 c = P7 (\h -> h (SatisfyF c))
>
> try7 :: Parser7 a -> Parser7 a
> try7 px = P7 (\h -> h (TryF (unP7 px h)))
>
> ap7 :: Parser7 (a -> b) -> Parser7 a -> Parser7 b
> ap7 pf px = P7 (\h -> h (ApF (unP7 pf h) (unP7 px h)))
>
> or7 :: Parser7 a -> Parser7 a -> Parser7 a
> or7 px py = P7 (\h -> h (OrF (unP7 px h) (unP7 py h)))

One benefit of this approach is that it allows the shallow embedding to be converted to a deep embedding.

> deep :: Parser7 a -> Parser4 a
> deep parser = unP7 parser In


Simillarly it is possible to convert a deep embedding into a parameterised shallow embedding.

> shallow :: Parser4 a -> Parser7 a
> shallow = cata shallowAlg
>
> shallowAlg :: ParserAlg Parser7 i
> shallowAlg (PureF x)     = pure7 x
> shallowAlg EmptyF        = empty7
> shallowAlg (SatisfyF c)  = satisfy7 c
> shallowAlg (TryF px)     = try7 px
> shallowAlg (ApF pf px)   = ap7 pf px
> shallowAlg (OrF px py)   = or7 px py

Being able to convert between both types of embedding,
demonstrates that deep and parameterised shallow embeddings are inverses of each other.


\subsection{Implicitly Parameterised Interpretations}

The previous parameterised implementation still required the algebra to be specified.
It would be helpful if it could be passed implicitly, if it can be determined from the type of the interpretation.
This is possible in Haskell through the use of a type class.

%format Parser8
%format pure8
%format empty8
%format satisfy8
%format try8
%format ap8
%format or8
%format Size8

> class Parser8 parser where
>   empty8    :: parser a
>   pure8     :: a -> parser a
>   satisfy8  :: (Char -> Bool)   -> parser Char
>   try8      :: parser a         -> parser a
>   ap8       :: parser (a -> b)  -> parser a -> parser b
>   or8       :: parser a         -> parser a -> parser a

> newtype Size8 i = Size {unSize :: Int} deriving Num

> instance Parser8 Size8 where
>   empty8      = 1
>   pure8 _     = 1
>   satisfy8 _  = 1
>   try8 px     = px + 1
>   ap8 pf px   = coerce pf + coerce px + 1
>   or8 px py   = px + py + 1

|coerce| allows for conversion between types that have the same runtime representation.
This is the case for |Size8| and |Int|.
To be able to reuse the previously defined algebras, a different type class can be defined.

%format Parser9

> class Parser9 parser where
>   alg :: ParserAlg parser i
>
> instance Parser9 Size8 where
>   alg = coerce . sizeAlg . imap coerce




\subsection{Modular Interpretations}

There may be times when adding extra combinators would be convenient, for example adding a 'many' operator that allows for
A modular technique to assembling DSLs would aid this process.

%format Empty10
%format Pure10
%format Satisfy10
%format Try10
%format Ap10
%format Or10
%format ParserF10
%format Parser10
%format aorb10
%format :+: = ":\!\!+\!\!:"


> data Empty10 (k :: * -> *) (a :: *) where
>   Empty10 :: Empty10 k a
>
> data Pure10 (k :: * -> *) (a :: *) where
>   Pure10 :: a -> Pure10 k a
>
> data Satisfy10 (k :: * -> *) (a :: *) where
>   Satisfy10 :: (Char -> Bool) -> Satisfy10 k Char
>
> data Try10 (k :: * -> *) (a :: *) where
>   Try10 :: k a -> Try10 k a
>
> data Ap10 (k :: * -> *) (a :: *) where
>   Ap10 :: k (a -> b) -> k a -> Ap10 k b
>
> data Or10 (k :: * -> *) (a :: *) where
>   Or10 :: k a -> k a -> Or10 k a


> data (f :+: g) (k :: * -> *) (a :: *) where
>   L :: f k a -> (f :+: g) k a
>   R :: g k a -> (f :+: g) k a
> infixr :+:
>
> instance (IFunctor f, IFunctor g)
>     => IFunctor (f :+: g) where
>   imap f (L x) = L (imap f x)
>   imap f (R y) = R (imap f y)

> type ParserF10  =    Empty10  :+:  Pure10  :+:  Satisfy10
>                 :+:  Try10    :+:  Ap10    :+:  Or10
>
> type Parser10 = Fix ParserF10


> aorb10 :: Parser10 Char
> aorb10 = In (R (R (R (R (R (Or10
>            (In (R (R (L (Satisfy10 (=='a'))))))
>            (In (R (R (L (Satisfy10 (=='b'))))))))))))


%format empty10
%format pure10
%format satisfy10
%format try10
%format ap10
%format or10
%format aorb10'
%format :<: = ":\prec:"


> class (IFunctor f, IFunctor g) => f :<: g where
>   inj :: f k a -> g k a
>
> instance IFunctor f => f :<: f where
>   inj = id
>
> instance {-# OVERLAPPING #-} (IFunctor f, IFunctor g) => f :<: (f :+: g) where
>   inj = L
>
> instance (IFunctor f, IFunctor g, IFunctor h, f :<: g) => f :<: (h :+: g) where
>   inj = R . inj

Smart constructors:

> empty10 :: (Empty10 :<: f) => Fix f a
> empty10 = In (inj Empty10)
>
> pure10 :: (Pure10 :<: f) => a -> Fix f a
> pure10 x = In (inj (Pure10 x))
>
> satisfy10 :: (Satisfy10 :<: f) => (Char -> Bool) -> Fix f Char
> satisfy10 c = In (inj (Satisfy10 c))
>
> try10 :: (Try10 :<: f) => Fix f a -> Fix f a
> try10 px = In (inj (Try10 px))
>
> ap10 :: (Ap10 :<: f) => Fix f (a -> b) -> Fix f a -> Fix f b
> ap10 pf px = In (inj (Ap10 pf px))
>
> or10 :: (Or10 :<: f) => Fix f a -> Fix f a -> Fix f a
> or10 px py = In (inj (Or10 px py))



> aorb10' :: (Or10 :<: f, Satisfy10 :<: f) => Fix f Char
> aorb10' = satisfy10 (== 'a') `or10` satisfy10 (== 'b')


%format sizeAlg10
%format size10


> class IFunctor f => SizeAlg f where
>   sizeAlg10 :: f Size8 i -> Size8 i
>
> instance (SizeAlg f, SizeAlg g) => SizeAlg (f :+: g) where
>   sizeAlg10 (L x) = sizeAlg10 x
>   sizeAlg10 (R y) = sizeAlg10 y
>
> instance SizeAlg Or10 where
>   sizeAlg10 (Or10 px py) = px + py + 1
>
> instance SizeAlg Satisfy10 where
>   sizeAlg10 (Satisfy10 _) = 1


> size10 :: SizeAlg f => Fix f a -> Size8 a
> size10 = cata sizeAlg10
>
> eval :: Size
> eval = coerce (size10 (aorb10' :: (Fix (Or10 :+: Satisfy10)) Char))





\bibliography{biblo}

\appendix
\section{Appendix}

%if False

> main :: IO ()
> main = undefined

%endif

> type Size = Int
> size :: Parser2 a -> Size
> size  Empty2        =  1
> size  (Pure2 _)     =  1
> size  (Satisfy2 _)  =  1
> size  (Try2 px)     =  1 +  size px
> size  (Ap2 pf px)   =  1 +  size pf  + size px
> size  (Or2 px py)   =  1 +  size px  + size py

%format Parser3
%format pure3
%format satisfy3
%format empty3
%format try3
%format ap3
%format or3
%format size3

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


> class IFunctor f where
>   imap :: (forall i . a i -> b i) -> f a i -> f b i
>
> newtype Fix f a = In (f (Fix f) a)
> cata :: IFunctor f => (forall i . f a i -> a i) -> Fix f i -> a i
> cata alg (In x) = alg (imap (cata alg) x)


> instance IFunctor Empty10 where
>   imap _ Empty10 = Empty10
>
> instance IFunctor Pure10 where
>   imap _ (Pure10 x) = Pure10 x
>
> instance IFunctor Satisfy10 where
>   imap _ (Satisfy10 c) = Satisfy10 c
>
> instance IFunctor Try10 where
>   imap f (Try10 px) = Try10 $ f px
>
> instance IFunctor Ap10 where
>   imap f (Ap10 pf px) = Ap10 (f pf) (f px)
>
> instance IFunctor Or10 where
>   imap f (Or10 px py) = Or10 (f px) (f py)


\end{document}
