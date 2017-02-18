\documentclass{article}
%include polycode.fmt
\usepackage[utf8]{inputenc}
\usepackage[autostyle]{csquotes}
\usepackage{hyperref,amsmath,listings}

\usepackage[
    backend=biber,
    natbib=true,
    url=true,
    doi=true,
    eprint=false
]{biblatex}

\addbibresource{Merkle.bib}

\title{Algorand-Compatible Merkle Tree Implementation}
\author{Jonn Mostovoy}
\date{February 2017}
\usepackage{geometry}
  \geometry{
  a4paper,
  total={170mm,257mm},
  left=20mm,
  top=20mm,
  }

\begin{document}

\maketitle

\section{Introduction}

Here we provide an implementation for Algorand-compatible
\cite{algorand} Merkle tree.  Important part of Algorand-compatible
Merkle trees is the way new elements are appended. For example, in
Merkle trees used in Certificate Transparency software
\cite{certitrans} are filled partially. When fifth value $ d_4 $ is
added to the list $ \vec{d} $, authenticated by a full 2-deep Merkle
tree $ T_4 $, Certificate Transparency version of Merkle trees adds a
node at depth 1, to be hashed with the previous Merkle tree root to
calculate new tree root. When value $ d_5 $ is added, values $ d_5 $
and $ d_4 $ are moved to depth 2. The process repeats till $ \lvert{}
\vec{d} \rvert{} = 8 $.  In Algorand, when $ d_4 $ is added, it's
added to depth 3, a special string $ e $ is added as its sibling, then
$ d_4 $ is hashed with $ e $ and stored at depth 2. Its sibling,
again, is a string $ e $. Finally, on the depth 1, $ T^{01}_5 = hash
((d_4 <> e) <> e) $ is stored. New root is a hash of previous root and
$T^{01}_5$.  This complication is required in order to denote the
nodes in tree $ T_i $ that don't have any children. It is helpful when
proofs for an append-only list are generated as elements are added to
this list. For more details on node insertion strategy, consult pages
50-and 51 of the paper \cite{algorand}, subsection “Efficient Block
Constructibility”.

\section{API and Imports}

\subsection{API}

Let's define API for Merkle Tree implementation.

\begin{code}
{-# LANGUAGE NamedFieldPuns #-}

module Algorand.Merkle
  (MerkleTree(..))
  where
\end{code}

\subsection{Imports}

We're using $ foldMap $ as a basis for $ Foldable $ implementation, so
we need to have Data.Monoid at our disposal.

\begin{code}
import Data.Monoid ((<>), mempty)
\end{code}

\section{MerkleTree}

\subsection{Data Type}

Our Merkle Tree is polymorphic both in block type (type variable $a$)
and in type of hash stored in nodes (type variable $b$). Rationale
behind block type polymorphism is clear. Rationale behind hash type
polymorphism is that not only no properties of Merkle Tree are bound
to the precise hash function used, but also sometimes it's worty to
harden the contents of nodes with information about depth to prevent
second preimage attack[?].

\begin{code}
data MerkleTree a b
    = MerkleTree { mValue :: b
                 , mLeft :: MerkleTree a b
                 , mRight :: MerkleTree a b }
    | MerkleLeaf { mValue :: b }
    | MerkleEmpty
\end{code}
It would be great if Haskell type system would allow us to trivially
express surjectivity constraint, then we could say something along the
lines of
\begin{verbatim}
data (Surjective a b) => MerkleTree a b
\end{verbatim}
But that constraint is impossible to meaningfully express in Haskell,
leaving it for the domain of dependently typed languages.

\subsection{Instances}

Arguably the most important instance for any tree is $Foldable$
\cite{foldtrav} as it provides us access to $toList$. Below we provide
a straight-forward implementation of $Foldable$ for MerkleTree with
block type $a$. As oposed to some implementations of $Foldable$ for
trees that authenticate lists, we don't discard information stored in
nodes of the tree.

\begin{code}
instance Foldable (MerkleTree a) where
    _ `foldMap` MerkleEmpty = mempty
    f `foldMap` MerkleLeaf{mValue} = f mValue
    f `foldMap` MerkleTree{mValue,mLeft,mRight} =
        (foldMap f mLeft) <> (f mValue) <> (foldMap f mRight)
\end{code}
Pretty much in the spirit of $Foldable$ instance, we define $Functor$
and $Traversable$ that, correspondingly, applies a function to each
value directly, and via $Applicative$ (enabling effectful applications).

\begin{code}
instance Functor (MerkleTree a) where
    _ `fmap` MerkleEmpty = MerkleEmpty
    f `fmap` MerkleLeaf{mValue} = MerkleLeaf (f mValue)
    f `fmap` MerkleTree{mValue,mLeft,mRight} =
        MerkleTree (f mValue) (f <$> mLeft) (f <$> mRight)

instance Traversable (MerkleTree a) where
    _ `traverse` MerkleEmpty = pure MerkleEmpty
    f `traverse` MerkleLeaf{mValue} = MerkleLeaf <$> f mValue
    f `traverse` MerkleTree{mValue,mLeft,mRight} =
        MerkleTree <$>
          (f mValue) <*> (traverse f mLeft) <*> (traverse f mRight)
\end{code}

\printbibliography

\end{document}
