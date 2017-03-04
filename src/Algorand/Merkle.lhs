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
\author{Jonn Mostovoy \\
       \href{mailto:jonn.mostovoy@@iohk.io}{jonn.mostovoy@@iohk.io}}
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Algorand.Merkle
  (MerkleTree(..)
  ,HashParams(..)
  ,Height(..)
  ,Index(..)
  ,leaf
  ,merkleTree
  ,append
  ,foldFront
  ,front
  ,find
  ,cofind
  ,auditProof
  ,auditVerify)
  where
\end{code}

\subsection{Imports}

We are using $ foldMap $ as a basis for $ Foldable $ implementation,
so we need to have Data.Monoid at our disposal. The only external
instrument we're using is $ toList $ to easily authenticate any
$ Foldable $ structure.

\begin{code}
import           Data.Foldable (toList)
import           Data.Monoid   (mempty, (<>))
\end{code}

\section{MerkleTree and Important API Functions}

\subsection{Data Type}

Our Merkle Tree is polymorphic both in block type (type variable $a$)
and in type of hash stored in nodes (type variable $b$). Rationale
behind block type polymorphism is clear. Rationale behind hash type
polymorphism is that not only no properties of Merkle Tree are bound
to the precise hash function used, but also sometimes it's worty to
harden the contents of nodes with information about depth to prevent
second preimage attack[?]. Interestingly, polymorphism in hashing also
contributes to the ease of testing, both manual and automated. Those
benefits come at an expense of an extra function argument for the most
of the functions that work with Merkle trees. Its type is $HashParams$
and it is a way to configure hashing. It requires user to provide
information about three fields, in order of declaration:
\begin{itemize}
    \item $hpHash$ tells how to transform a data block into hash
    \item $hpConcat$ tells how to add together two hashes and hash them
    \item $hpEmpty$ tells how to produce designated string $e$
\end{itemize}
\begin{code}
data MerkleTree a b
    = MerkleTree { mValue :: b
                 , mLeft :: MerkleTree a b
                 , mRight :: MerkleTree a b }
    | MerkleEmpty
    deriving (Eq)

data HashParams a b = HashParams
    { hpHash :: a -> b
    , hpConcat :: b -> b -> b
    , hpEmpty :: b
    }

type MT a b = MerkleTree a b
\end{code}
It would be great if Haskell type system would allow us to trivially
express surjectivity constraint, then we could say something along the
lines of

\begin{verbatim}
data (Surjective a b) => MerkleTree a b
\end{verbatim}
But that constraint is impossible to meaningfully express in Haskell,
leaving it for the domain of dependently typed languages. Finally, it is
worth noting a $HashParams$ configuration that is very useful for
testing.
\begin{verbatim}
HashParams id (++) "e"
\end{verbatim}
In this configuration hash function is identity, concatenation of
hashes is list concatenation and empty string is an arbitrary string.

\subsection{API Functions}

First, we define a smart constructor for Merkle Tree that
authenticates any $Foldable$. The idea is to build the tree layer by
layer. To get initial layer, we promote data blocks that are given to
us as an argument to Merkle leaves. Inductively, given a layer, we
produce next layer by creating Merkle nodes of previous layer pair by
pair, adding a node with no children holding designated string $e$, if
the last node in the previous layer does not have a pair (has an odd
index). If there is one node left in the previous layer, it is the
root and it gets returned. If there are zero nodes in a layer, an
empty tree is returned.

\begin{code}
leaf :: b -> MT a b
leaf x = MerkleTree x MerkleEmpty MerkleEmpty

merkleTree :: Foldable f => HashParams a b -> f a -> MT a b
merkleTree HashParams{hpHash,hpConcat,hpEmpty} =
    buildTree . mkLeaves
  where
    mkLeaves = foldMap (pure . leaf . hpHash)
    buildTree [] = MerkleEmpty
    buildTree [y] = y
    buildTree ys = buildTree $ reverse $ mkLayer ys []
    mkLayer [] acc = acc
    mkLayer [x] acc =
        (MerkleTree ((hpConcat (mValue x) hpEmpty)) x (leaf hpEmpty)) : acc
    mkLayer (x:y:rest) acc =
        mkLayer rest $ (MerkleTree (hpConcat (mValue x) (mValue y)) x y) : acc
\end{code}
Now we define a way to append a new data block to the authenticated
list. To begin with, we define a helper-function that returns the
right front of the tree. In case we find $e$ in the right front, we
pick the left child of the current node, tagging the entry in the
output list. In our particular implementation, we use $Either$ to tag
left and right children in a straight-forward way. Then we implement
$append$ function itself. Append function works in two modes — $Insert$ and
$Update$. When the tree has even amount of nodes in a layer, we keep woking
in $Insert$ mode, adding new element to the left, when the layer has odd
amount of nodes, we switch to $Update$, updating the leftmost $e$-node.
If we are already in $Update$ mode, we know that changes to the previous
layer impact current layer, so we update a node in current layer appropriately.
When there is only one element left in the list of values generated by $front$
function, we return its updated version if we are in $Update$ mode and create
new root, returning it if we are in $Insert$ mode.

\begin{code}

front
    :: Eq b
    => HashParams a b
    -> MT a b
    -> [Either (MT a b) (MT a b)]
front h = foldFront h (:) []

append :: Eq b => HashParams a b -> a -> MerkleTree a b -> MerkleTree a b
append hp d mt0 =
    f (front hp mt0) $ Insert $ (leaf . h) d
  where
    f [] (Insert mt) = mt
    f [] (Update mt) = f [] (Insert mt) -- Shouldn't happen
    f [Right root] (Insert mt) =
        MerkleTree (val root <^> val mt) root mt
    f [Right _root] (Update mt) = mt
    f [Left root] mt = f [Right root] mt -- Shouldn't happen
    f (Right _:xs) (Insert mt) =
        f xs (Insert $ MerkleTree (val mt <^> e) mt $ leaf e)
    f (Left x:xs) (Insert mt) =
        f xs (Update $ MerkleTree (val x <^> val mt) x mt)
    f (Right _:Right p:xs) (Update mt) =
        f (Right p:xs) (Update $ MerkleTree (val (l p) <^> val mt) (l p) mt)
    f (Right _:Left p:xs) (Update mt) =
        f (Left p:xs) (Update $ MerkleTree (val (l p) <^> val mt) (l p) mt)
    f (Left _:xs) (Update mt) =
        f xs (Update $ MerkleTree (val mt <^> e) mt $ leaf e)
    l = mLeft
    val = mValue
    h = hpHash hp
    (<^>) = hpConcat hp
    e = hpEmpty hp
\end{code}
Finally, we introduce a function to generate a proof of membership of
$i^{th}$ element in a tree of height $h$. As you can see from the
implementation, it's the same as $cofind$, which is a function that
goes along the path to $i^{th}$ element in a $h$-high tree, remembering
the siblings of the nodes it passed through.

\begin{code}
auditProof :: Height -> Index -> MT a b -> Maybe [Either (MT a b) (MT a b)]
auditProof = cofind

auditVerify
    :: Eq b
    => HashParams a b -> b -> MT a b -> [Either (MT a b) (MT a b)] -> Bool
auditVerify _ root x [] = root == mValue x
auditVerify hp@HashParams{hpConcat} root x (Left p:ps) =
    auditVerify hp root (leaf (mValue p `hpConcat` mValue x)) ps
auditVerify hp@HashParams{hpConcat} root x (Right p:ps) =
    auditVerify hp root (leaf (mValue x `hpConcat` mValue p)) ps
\end{code}

\section{Fundamental Instances}

Arguably the most important instance for any tree is $Foldable$
\cite{foldtrav} as it provides us access to $toList$. Below we provide
a straight-forward implementation of $Foldable$ for MerkleTree with
block type $a$. As oposed to some implementations of $Foldable$ for
trees that authenticate lists, we don't discard information stored in
nodes of the tree.

\begin{code}
instance Foldable (MerkleTree a) where
    _ `foldMap` MerkleEmpty = mempty
    f `foldMap` MerkleTree{mValue,mRight = MerkleEmpty,mLeft = MerkleEmpty} =
        f mValue
    f `foldMap` MerkleTree{mValue,mLeft,mRight} =
        (foldMap f mLeft) <> (f mValue) <> (foldMap f mRight)
\end{code}
Pretty much in the spirit of $Foldable$ instance, we define $Functor$
and $Traversable$ that, correspondingly, applies a function to each
value directly, and via $Applicative$ (enabling effectful applications).

\begin{code}
instance Functor (MerkleTree a) where
    _ `fmap` MerkleEmpty = MerkleEmpty
    f `fmap` MerkleTree{mValue,mRight = MerkleEmpty,mLeft = MerkleEmpty} =
        leaf (f mValue)
    f `fmap` MerkleTree{mValue,mLeft,mRight} =
        MerkleTree (f mValue) (f <$> mLeft) (f <$> mRight)

instance Traversable (MerkleTree a) where
    _ `traverse` MerkleEmpty = pure MerkleEmpty
    f `traverse` MerkleTree{mValue,mRight = MerkleEmpty,mLeft = MerkleEmpty} =
        MerkleTree <$> f mValue <*> pure MerkleEmpty <*> pure MerkleEmpty
    f `traverse` MerkleTree{mValue,mLeft,mRight} =
        MerkleTree <$> (f mValue) <*> (traverse f mLeft) <*>
        (traverse f mRight)
\end{code}
Last, but not least, $Show$ instance!

\begin{code}
instance Show b => Show (MerkleTree a b) where
    show t = "MerkleTree<" ++ show (toList t) ++ ">"
\end{code}

\subsection{Helper Functions and Data Types}
We can characterize helper functions we present as dirty. It is
obvious to the author that a better generalization exists, but
for the sake of swiftness of implementation, author presents
functions $foldFront$ and $path$. $foldFront$, given a function that goes
from a node marked with $Either$ (which, as reader might remember,
marks whether or not there is an $e$-node to the right of the leftmost
filled node or not) and accumulated value of any type $c$ to the new
value of type $c$ folds the front of a Merkle Tree into a value of type $c$.
$path$, given the height of a tree and an index of a leaf, traverses the
tree down to this node, applying a function to memorize the path.
Function that memorizes the path gets the parent node and a direction
encoded with $Either () ()$ and returns a tagged Merkle node that will
be remembered by the output. Author apologizes for the lack of elegance
in helper functions and hopes to generalize those in a later revision
of this module. At the end of this listing, data types are provided, purpose
of which is self-explanatory.

\begin{code}
foldFront :: Eq b
          => HashParams a b
          -> (Either (MT a b) (MT a b) -> c -> c)
          -> c
          -> MT a b
          -> c
foldFront HashParams{hpEmpty} f0 acc0 mt0 =
    g Nothing f0 acc0 mt0
  where
    g _ _ acc MerkleEmpty = acc
    g Nothing f acc mt = g (Just mt) f (f (Right mt) acc) (r mt)
    g (Just tip) f acc mt
        | val mt == hpEmpty
        = g (Just $ l tip) f (f (Left $ l tip) acc) (r $ l tip)
        | otherwise
        = g (Just mt) f (f (Right mt) acc) (r mt)
    l = mLeft
    r = mRight
    val = mValue

find :: Height
     -> Index
     -> MT a b
     -> Maybe [Either (MT a b) (MT a b)]
find = path f
    where
      f mt (Left ()) = (Left . mLeft) mt
      f mt (Right ()) = (Right . mRight) mt

cofind :: Height
       -> Index
       -> MT a b
       -> Maybe [Either (MT a b) (MT a b)]
cofind = path f
    where
      f mt (Left ()) = (Right . mRight) mt
      f mt (Right ()) = (Left . mLeft) mt

path :: (MT a b -> Either () () -> Either (MT a b) (MT a b))
     -> Height
     -> Index
     -> MT a b
     -> Maybe [Either (MT a b) (MT a b)]
path mkp height0 target0 =
    let h = mkHeight height0
        t = mkIndex target0
    in f (1, 2 ^ (h - 1), 2 ^ h) t []
  where
    f (lf,c,rt) target acc mt
      | target == lf || target == rt = Just acc
      | lf <= target && target <= c =
          f (upd lf c) target (mkp mt (Left ()) : acc) (mLeft mt)
      | c < target && target <= rt =
          f (upd c rt) target (mkp mt (Right ()) : acc) (mRight mt)
      | otherwise = Nothing
    upd from to =
        let delta = (to - from) `div` 2
        in (from, from + delta, to)


data Append a = Insert a | Update a
newtype Height = Height {mkHeight :: Int}
newtype Index = Index {mkIndex :: Int}
\end{code}

\printbibliography

\end{document}
