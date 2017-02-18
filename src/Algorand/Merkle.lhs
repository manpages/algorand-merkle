\documentclass{article}
%include polycode.fmt
\usepackage[utf8]{inputenc}
\usepackage[autostyle]{csquotes}
\usepackage{hyperref,amsmath}

\usepackage[
    backend=biber,
    natbib=true,
    url=false,
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

Here we provide an implementation for Algorand-compatible Merkle tree.
Important part of Algorand-compatible Merkle trees is the way new
elements are appended. For example, in Merkle trees used in
Certificate Transparency software \cite{certitrans} are filled
partially. When fifth value $ d_4 $ is added to the list $ \vec{d} $,
authenticated by a full 2-deep Merkle tree $ T_4 $, Certificate
Transparency version of Merkle trees adds a node at depth 1, to be
hashed with the previous Merkle tree root to calculate new tree
root. When value $ d_5 $ is added, values $ d_5 $ and $ d_4 $ are
moved to depth 2. The process repeats till $ \lvert{} \vec{d} \rvert{}
= 8 $.
In Algorand, when $ d_4 $ is added, it's added to depth 3, a special
string $ e $ is added as its sibling, then $ d_4 $ is hashed with $ e
$ and stored at depth 2. Its sibling, again, is a string $ e
$. Finally, on the depth 1, $ T^{01}_5 = hash ((d_4 <> e) <> e) $ is
stored. New root is a hash of previous root and $T^{01}_5$.
This complication is required in order to denote the nodes in tree $
T_i $ that don't have any children. It is helpful while proofs for an
append-only list are generated as elements are added to this list.

\begin{code}
{-# LANGUAGE MultiParamTypeClasses #-}

module Algorand.Merkle
  (MerkleTree(..))
  where

data MerkleTree a b
    = MerkleTree { mValue :: b
                 , mLeft :: MerkleTree a b
                 , mRight :: MerkleTree a b}
    | MerkleLeaf { mValue :: b}
\end{code}

\section{References}

\printbibliography

\end{document}
