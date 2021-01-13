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

\usepackage{todonotes}
\usepackage{tikz-cd}


\title{\vspace{-10mm}An Overview of \citetalias{embedding}\vspace{-4mm}}
\author{Riley Evans (re17105)}
\date{\vspace{-3mm}}


%include polycode.fmt
%include forall.fmt
%include spacing.fmt

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


In this overview a small parser combinator language embedded into Haskell will be used.
This language brings one key feature that was not described in the paper: how to apply these techniques to a typed language.
Only a minimal functionally complete set of combinators have been included in the language to keep it simple.
However, all other combinators usually found in a combinator language can be constructed from this set.



\section{Background}

\subsection{DSLs}

A Domain Specific Language (DSL) is a programming language that has a specialised domain or use-case.
This differs from a General Purpose Language (GPL), which can be applied across a larger set of domains.
DSLs can be split into two different categories: standalone and embedded. Standalone DSLs require their own compiler and typically have their own syntax.
Embedded DSLs use an exisiting language as a host, therefore they use the syntax and compiler from that language.
This means that they are easier to maintain and are often quicker to develop than standalone DSLs.

An embedded DSL can be implemented with two main techniques.
Firstly, a deep approach can be taken, this means that terms in the DSL will construct an Abstract Syntax Tree (AST) as a host language datatype.
This can then be used to apply optimisations and then evaluated.
A second approach known as a shallow embedding, is to define the terms as first class components of the language. An example of this could be a function in Haskell. This approach avoids the creation of an AST.


\subsection{Parsers}

A parser is a used to convert a series of tokens into another language.
For example converting a string into a Haskell datatype.
Parser combinators provide a flexible approach to constructing parsers.
Unlike parser generators, a combinator library is embedded within a host language: using combinators to construct the grammar.
This makes it a suitable to demonstrate the techniques described in this paper for folding the DSL to create parsers.

The language is made up of 6 terms, they provide all the essential operations needed in a parser.

%if False

> type Parser a = Int

%endif

\pagebreak

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


A deep embedding of this parser language is defined in the algebraic datatype:

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


This can be interpreted by defining a function such as |size|, which finds the size of the AST used to construct the parser.
|size| interprets the deep embedding, by folding over the datatype.
See the appendix~\ref{app:shallow-size} for how to add an interpretation with a shallow embedding.

> type Size = Int
> size :: Parser2 a -> Size
> size  Empty2        =  1
> size  (Pure2 _)     =  1
> size  (Satisfy2 _)  =  1
> size  (Try2 px)     =  1 +  size px
> size  (Ap2 pf px)   =  1 +  size pf  + size px
> size  (Or2 px py)   =  1 +  size px  + size py

\section{Folds}

It is possible to capture the shape of an abstract datatype as a |Functor|.
The use of a |Functor| allows for the specification of where a datatype recurses.
There is, however, one problem: a |Functor| expressing the parser language is required to be typed.
Parsers require the type of the tokens being parsed.
For example, a parser reading tokens that make up an expression could have the type |Parser Expr|.
A |Functor| does not retain the type of the parser. Instead a type class called |IFunctor| will be used,
which is able to maintain the type indicies~\cite{mcbride2011functional}.
This can be thought of as a functor transformer:
it is able to change the structure of a functor whilst preserving the values inside it.

> class IFunctor iF where
>   imap :: (forall a . f a -> g a) -> iF f a -> iF g a


The shape of |Parser2|, can be seen in |ParserF| where the |f a| marks the recursive spots.

> data ParserF (f :: * -> *) (a :: *) where
>   EmptyF   :: ParserF f a
>   PureF    :: a               -> ParserF f a
>   SatisfyF :: (Char -> Bool)  -> ParserF f Char
>   TryF     :: f a             -> ParserF f a
>   ApF      :: f (a -> b)      -> f a   -> ParserF f b
>   OrF      :: f a             -> f a   -> ParserF f a

The |IFunctor| instance can be found in the appendix~\ref{app:ifunctor-parserf}.
It follows the same structure as a standard |Functor| instance.

%format Parser4

|Fix| is used to get the fixed point of a functor.
It provides the structure needed to allow the datatype to recursive.

> newtype Fix iF a = In (iF (Fix iF) a)

|Parser4| is the fixed point of |ParserF|.

> type Parser4 a = Fix ParserF a


A mechanism is now required for folding this abstract datatype.
This is possible through the use of a \textit{catamorphism}, which is a generalised way of folding an abstract datatype.
The commutative diagram below describes how a \textit{catamorphism} can be defined.
Firstly, a layer of |Fix| is peeled off by removing an |In| to give |iF (Fix iF) a|.
Then a recursive call is made to fold the structure below in the AST.
This results in a item of type |iF f a|.
Finally, an algebra is applied to fold this layer of the datatype, resulting in a item of type |f a|.

\begin{figure}[h]
\centering
\begin{tikzcd}[column sep=huge]
|iF (Fix iF) a|  \arrow[r, "|imap (cata alg)|"] \arrow[d, shift left=0.15cm, "|In|"] & |iF f a| \arrow[d, "|alg|"]\\
|Fix iF a|       \arrow[r, "|cata alg|"]        \arrow[u, shift left=0.15cm, "|inop|"]        & |f a|
\end{tikzcd}
\end{figure}


|cata| is able to fold a |Fix iF a| and produce an item of type |f a|.
It uses the algebra argument as a specification of how to fold the input datatype.


> cata :: IFunctor iF => (forall a . iF f a -> f a) -> Fix iF a -> f a
> cata alg (In x) = alg (imap (cata alg) x)


Since the resulting type of |cata| for an |IFunctor| is |f a|, this requires the output to be a |Functor|.
One example of this could be |Fix ParserF|.
However, in the case that the datatype would like to be folded into something that is not a functor,
or has kind |*|, then additional infrastructure is needed.
There are two methods to allow this to take place.
A new type could be defined for each output type that has a phantom type parameter. For example:

%format Size'

> newtype Size' i = Size' {unSize :: Size} deriving Num

However, this could lead to lots of new type definitions.
To avoid this the constant functor can be used.
It allows a type with kind |*| to have kind |* -> *|, in a similar way to how the |const| function works.


> newtype C a k = C {unConst :: a}


Now, all the building blocks have been defined that allow for the folding of the parser DSL.
|size| can be redefined as a fold, that is determined by the |sizeAlg|.
Due to parsers being a typed language, a constant functor is required to preserve the type indices.

%format size4

> type ParserAlg f a = ParserF f a -> f a
>
> sizeAlg :: ParserAlg (C Size) a
> sizeAlg EmptyF         = C 1
> sizeAlg (PureF     _)  = C 1
> sizeAlg (SatisfyF  _)  = C 1
> sizeAlg (TryF (C n))   = C (n + 1)
> sizeAlg (ApF (C pf) (C px)) = C (pf + px + 1)
> sizeAlg (OrF (C px) (C py)) = C (px + py + 1)
>
> size4 :: Parser4 a -> Size
> size4 = unConst . cata sizeAlg


\subsection{Multiple Interpretations}

In DSLs it is common to want to evaluate multiple interpretations.
For example, a parser may also want to know the maximum number of characters it will read (maximum munch).
In a deep embedding, this is simple: a second algebra can be defined.

%format maxMunch4

> type MM = Int
>
> mmAlg :: ParserAlg (C MM) a
> mmAlg EmptyF         = C 0
> mmAlg (PureF _)      = C 0
> mmAlg (SatisfyF c)   = C 1
> mmAlg (TryF (C px))  = C px
> mmAlg (ApF (C pf) (C px))  = C (pf + px)
> mmAlg (OrF (C px) (C py))  = C (max px py)
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
> smmAlg EmptyF              = C (1,      0)
> smmAlg (PureF _)           = C (1,      0)
> smmAlg (SatisfyF c)        = C (1,      1)
> smmAlg (TryF (C (s, mm)))  = C (s + 1,  mm)
> smmAlg (ApF  (C (s, mm)) (C (s', mm')))
>   = C (s + s' + 1, mm + mm')
> smmAlg (OrF  (C (s, mm)) (C (s', mm')))
>   = C (s + s' + 1, max mm mm')


It is possible to take an alegbra and convert it into a shallow embedding.
This is possible by setting the shallow embedding equal to the result of the algebra,
with the corresponding constructor from the deep embedding, for example:

%format ap5
%format or5

> ap5 pf px = smmAlg (ApF pf px)
> or5 px py = smmAlg (OrF px py)


\subsection{Dependent Interpretations}

In a more complex parser combinator library that perform optimisations on a deep embedding,
it could also be possible that there is a primary fold that depends on other secondary folds on parts of the AST.
Folds such as this are named \textit{zygomorphisms}~\cite{Fokkinga1989TuplingAM} - a special case of a \textit{mutomorphism} -
they can be implemented by tupling the functions in the fold.
\citet{parsley} makes use of a \textit{zygomorphism} to perform consumption analysis.


\subsection{Context-sensitive Interpretations}

Parsers themselves inherently require context sensitive interpretations - what can be parsed will
depend on what has previously been parsed.

A parser can be implemented with an accumulating fold.
An accumulating fold forms series of nested functions, that collapse to give a final value once the base case has been applied.
A simple example of an accumulating fold could be, implementing |foldl| in terms of |foldr|.


> foldl :: (b -> a -> b) -> b -> [a] -> b
> foldl f b as = foldr (\a g x -> g (f x a)) id as b

A simple example of |foldl| can be considered.

\begin{spec}
    foldl (+) 0 [1, 2]
==
    (\x->(\x-> id (x+2)) (x+1)) 0
\end{spec}

Yoda~\cite{wuYoda} is a simple non-deterministic parser combinator library.
The combinators are used to produce a function of type |parser :: String -> [(a, String)]|.
Similarities can be drawn from the previous example, the combinators form the first part of the example where a function is constructed of lambdas.
The base case |0| of the fold is then passed into the constructed function, this similar to how a string is passed into the parsing function.
The accumulating fold for Yoda, is implemented by |yAlg|.

%format ts'
%format ts''

> newtype Y a = Y {unYoda :: String -> [(a, String)]}
>
> yAlg :: ParserAlg Y a
> yAlg  EmptyF        = Y (const [])
> yAlg  (PureF x)     = Y (\ts -> [(x, ts)])
> yAlg  (SatisfyF c)  = Y (\ case
>       []       -> []
>       (t:ts')  -> [(t, ts') | c t])
> yAlg  (TryF px)     = px
> yAlg  (ApF (Y pf) (Y px)) = Y (\ts ->
>       [(f x, ts'')  |   (f,  ts')   <- pf ts
>                     ,   (x,  ts'')  <- px ts'])
> yAlg  (OrF (Y px) (Y py)) = Y (\ts -> px ts ++ py ts)
>
> parse :: Parser4 a -> String -> [(a, String)]
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
%format size7

Previously, when defining multiple interpretations in a shallow embedding, a tuple was used.
However, this does not extend well when many interpretations are needed.
Large tuples tend to lack good language support and will become messy to work with.
It would be beneficial if a shallow embedding could be parameterised to take an interpretation in the form of an algebra.

|Parser7| allows for this approach,
the shallow embedding is made up of first class functions that require an algebra argument.
This algebra describes how the shallow embedding should fold the structure.
The full definitions can be found in Appendix~\ref{app:parser7-constructors}.

> newtype Parser7 a = P7
>   {unP7 :: forall f . ( forall a . ParserAlg f a) -> f a}
>
> satisfy7 :: (Char -> Bool) -> Parser7 Char
> satisfy7 c = P7 (\h -> h (SatisfyF c))
>
> or7 :: Parser7 a -> Parser7 a -> Parser7 a
> or7 px py = P7 (\h -> h (OrF (unP7 px h) (unP7 py h)))


Then, for example, to find the size of a parser:

> size7 :: Parser7 a -> Size
> size7 p = unConst (unP7 p sizeAlg)


One benefit of this approach is that it allows the shallow embedding to be converted to a deep embedding.

> deep :: Parser7 a -> Parser4 a
> deep parser = unP7 parser In


Simillarly it is possible to convert a deep embedding into a parameterised shallow embedding.
Where |shallowAlg| is setting each constructor to the corresponding shallow function - this can be seen in Appendix~\ref{app:shallowalg}.

> shallow :: Parser4 a -> Parser7 a
> shallow = cata shallowAlg




Being able to convert between both types of embedding,
demonstrates that deep and parameterised shallow embeddings are inverses of each other.


\subsection{Implicitly Parameterized Interpretations}

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
>   pure8     :: a                -> parser a
>   satisfy8  :: (Char -> Bool)   -> parser Char
>   try8      :: parser a         -> parser a
>   ap8       :: parser (a -> b)  -> parser a -> parser b
>   or8       :: parser a         -> parser a -> parser a


> instance Parser8 Size' where
>   empty8      = Size' 1
>   pure8 _     = Size' 1
>   satisfy8 _  = Size' 1
>   try8 px     = Size' (unSize px  + 1)
>   ap8 pf px   = Size' (unSize pf  + unSize px  + 1)
>   or8 px py   = Size' (unSize px  + unSize py  + 1)

%|coerce| allows for conversion between types that have the same runtime representation.
%This is the case for |Size8| and |Int|.

To be able to reuse the previously defined algebras, a different type class can be defined.

%format Parser9

> class Parser9 parser where
>   alg :: ParserAlg parser a
>
> instance Parser9 Size' where
>   alg = Size' . unConst . sizeAlg . imap (C. unSize)




\subsection{Modular Interpretations}

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

There may be times when adding extra combinators would be convenient.
For example, adding a `string' operator.
A modular technique for assembling DSLs would aid this process.
This approach is described in Data types à la carte~\cite{datatypesalacarte}.
An |:+:| operator can be defined to specify a choice between constructors.

> data (iF :+: iG) (f :: * -> *) (a :: *) where
>   L :: iF f a -> (iF :+: iG) f a
>   R :: iG f a -> (iF :+: iG) f a
> infixr :+:
>
> instance  (IFunctor iF, IFunctor iG)
>           => IFunctor (iF :+: iG) where
>   imap  f (L x)  = L  (imap  f  x)
>   imap  f (R y)  = R  (imap  f  y)


For each constructor that is required the datatype and |IFunctor| instance can be defined.

> data Ap10 (f :: * -> *) (a :: *) where
>   Ap10 :: f (a -> b) -> f a -> Ap10 f b
>
> instance IFunctor Ap10 where
>   imap f (Ap10 pf px) = Ap10 (f pf) (f px)

All datatypes and instances can be found in Appendix~\ref{app:modular-dtypes-ifunctors}

The datatypes are now summed together to form a single |ParserF10| type.

> type ParserF10  =    Empty10  :+:  Pure10  :+:  Satisfy10
>                 :+:  Try10    :+:  Ap10    :+:  Or10
>
> type Parser10 = Fix ParserF10

There is however, one problem with this approach: there is now a mess of |L| and |R|'s.
This makes this approach inconvenient to use.

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

Data types à la carte~\cite{datatypesalacarte}, however, describes a technique that allows for the injection of these |L|'s and |R|'s.
The notion of subtypes between functors, can be specified using the |:<:| operator.


> class (IFunctor iF, IFunctor iG) => iF :<: iG where
>   inj :: iF f a -> iG f a
>
> instance IFunctor iF => iF :<: iF where
>   inj = id

\newpage

> instance  {-# OVERLAPPING #-}
>           (IFunctor iF, IFunctor iG)
>           => iF :<: (iF :+: iG) where
>   inj  = L
>
> instance  (IFunctor iF, IFunctor iG,
>           IFunctor iH, iF :<: iG)
>           => iF :<: (iH :+: iG) where
>   inj = R . inj


Smart constructors are defined that allow for the |L|'s and |R|'s to be injected.
Two examples are given, the other smart constructors can be found in Appendix~\ref{app:modular-smart-constructors}

> satisfy10 :: (Satisfy10 :<: iF)  => (Char -> Bool)
>                                 -> Fix iF Char
> satisfy10 c = In (inj (Satisfy10 c))
>
> or10 :: (Or10 :<: iF) => Fix iF a -> Fix iF a -> Fix iF a
> or10 px py = In (inj (Or10 px py))

Now the smart constructors can be used to form an expression |aorb10'|.
The type contraints on this expression allow for |f| to be flexible, so long as |Or10| and |Satisfy10| are subtypes of the functor |f|.

> aorb10' :: (Or10 :<: iF, Satisfy10 :<: iF) => Fix iF Char
> aorb10' = satisfy10 (== 'a') `or10` satisfy10 (== 'b')


%format sizeAlg10
%format size10

To be able to give an interpretation an algebra is still required.
Simillarly to the constructors the algebra needs to be modularized.
A type class can be defined that provides the algebra to fold each constructor.



> class IFunctor iF => SizeAlg iF where
>   sizeAlg10 :: iF Size' a -> Size' a
>
> instance  (SizeAlg iF, SizeAlg iG)
>           => SizeAlg (iF :+: iG) where
>   sizeAlg10 (L x) = sizeAlg10 x
>   sizeAlg10 (R y) = sizeAlg10 y

One benefit to this approach is that if an interpretation is only needed for parsers that use |or10| and |satisfy10|,
then only those instances need to be defined.
Take calculating the size of the parser |aorb10'|, only the two instances need to be defined to do so.


> instance SizeAlg Or10 where
>   sizeAlg10 (Or10 px py) = px + py + 1
>
> instance SizeAlg Satisfy10 where
>   sizeAlg10 (Satisfy10 _) = 1

> size10 :: SizeAlg iF => Fix iF a -> Size' a
> size10 = cata sizeAlg10
>
> eval :: Size
> eval = unSize  (size10 (aorb10' :: (
>                Fix (Or10 :+: Satisfy10)) Char))

%format Circuit11
%format WidthAlg11
%format Fan11
%format Stretch11

The type of |aorb10'| is required to be specified.
This is so that the compiler knows the top level functor being used and the constructors included in it.
There could possibly an error in the paper here, as it states that only instances for |Fan11| and |Stretch11| need to be defined.
However, it sets the type for |stretchfan| to be |Circuit11|.
This requires that the |WidthAlg11| instances be defined for all constructors in |Circuit11|.
To rectify this type error |stretchfan| should be given the type |stretchfan :: Fix (Fan11 :+: Stretch11)|.



\section{Conclusion}
This overview has walked through the techniques described in the paper and applied them to a previously unconsidered case - typed DSLs.
This now allows the techniques in the paper to be taken advantage of in typed DSLs such as parser combinators.
This is done through the use of an |IFunctor| and special instances of |Fix| and |cata|.


\bibliography{biblo}

\appendix
\section{Appendix}

%if False

> main :: IO ()
> main = undefined

%endif

\subsection{Shallow Embedding of |size|}
\label{app:shallow-size}

%format Parser3
%format pure3
%format satisfy3
%format empty3
%format try3
%format ap3
%format or3
%format size3

> type Parser3 a = Int
> pure3     _  = 1
> satisfy3  _  = 1
> empty3       = 1
> try3  px     = px  + 1
> ap3   pf px  = pf  + px  + 1
> or3   px py  = px  + py  + 1
>
> size3 :: Parser3 a -> Size
> size3 = id

\subsection{|IFunctor| instance of |ParserF|}
\label{app:ifunctor-parserf}

> instance IFunctor ParserF where
>   imap _ EmptyF        = EmptyF
>   imap _ (PureF x)     = PureF     x
>   imap _ (SatisfyF c)  = SatisfyF  c
>   imap f (TryF px)     = TryF  (f px)
>   imap f (ApF pf px)   = ApF   (f pf)  (f px)
>   imap f (OrF px py)   = OrF   (f px)  (f py)


\subsection{Constructors for a Parameterized Shallow Embedding}
\label{app:parser7-constructors}

> empty7 :: Parser7 a
> empty7 = P7 (\h -> h EmptyF)
>
> pure7 :: a -> Parser7 a
> pure7 x = P7 (\h -> h (PureF x))
>
> try7 :: Parser7 a -> Parser7 a
> try7 px = P7 (\h -> h (TryF (unP7 px h)))
>
> ap7 :: Parser7 (a -> b) -> Parser7 a -> Parser7 b
> ap7 pf px = P7 (\h -> h (ApF (unP7 pf h) (unP7 px h)))


\subsection{Converting from Deep to a Parameterized Shallow Embedding}
\label{app:shallowalg}

> shallowAlg :: ParserAlg Parser7 a
> shallowAlg EmptyF        = empty7
> shallowAlg (PureF x)     = pure7 x
> shallowAlg (SatisfyF c)  = satisfy7 c
> shallowAlg (TryF px)     = try7 px
> shallowAlg (ApF pf px)   = ap7 pf px
> shallowAlg (OrF px py)   = or7 px py


\subsection{Datatypes and IFunctor Instances for a Modular Interpretation}
\label{app:modular-dtypes-ifunctors}

> data Empty10 (f :: * -> *) (a :: *) where
>   Empty10 :: Empty10 f a
>
> data Pure10 (f :: * -> *) (a :: *) where
>   Pure10 :: a -> Pure10 f a
>
> data Satisfy10 (f :: * -> *) (a :: *) where
>   Satisfy10 :: (Char -> Bool) -> Satisfy10 f Char
>
> data Try10 (f :: * -> *) (a :: *) where
>   Try10 :: f a -> Try10 f a
>
> data Or10 (f :: * -> *) (a :: *) where
>   Or10 :: f a -> f a -> Or10 f a

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
> instance IFunctor Or10 where
>   imap f (Or10 px py) = Or10 (f px) (f py)

\subsection{Smart Constructors to Inject |L| and |R|'s}
\label{app:modular-smart-constructors}

> empty10 :: (Empty10 :<: iF) => Fix iF a
> empty10 = In (inj Empty10)
>
> pure10 :: (Pure10 :<: iF) => a -> Fix iF a
> pure10 x = In (inj (Pure10 x))
>
> try10 :: (Try10 :<: iF) => Fix iF a -> Fix iF a
> try10 px = In (inj (Try10 px))
>
> ap10 :: (Ap10 :<: iF) => Fix iF (a -> b) -> Fix iF a -> Fix iF b
> ap10 pf px = In (inj (Ap10 pf px))





\end{document}
