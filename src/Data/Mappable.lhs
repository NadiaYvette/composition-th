\documentclass{article}
%include polycode.fmt
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage[backend=biber]{biblatex}
\usepackage{comment}
\usepackage{url}
\begin{document}
%if False
\begin{code}
module Data.Mappable where
import           "base"  Numeric.Natural (Natural)
import qualified         Data.Mappable.TH as
  Mappable (mkFmap, mkMapM, mkOnN, mkPassN)
import qualified "extra" Control.Monad.Extra as
  Monad (concatMapM)
\end{code}
\begin{spec}
import qualified "singletons-base" Data.Singletons.Base.TH as
  Base (Apply)
import qualified "singletons-base" Data.List.Singletons as
  List (Foldl)
import qualified "base"            Data.Foldable as
  Fold ()
import           "base"            Data.Kind (Type)
import qualified "base"            Data.Traversable as
  Trav ()
\end{spec}
%endif
\begin{code}
$(Monad.concatMapM Mappable.mkFmap [2 .. 7 :: Natural])
\end{code}

\begin{code}
$(Monad.concatMapM Mappable.mkMapM [1 .. 7 :: Natural])
\end{code}

\begin{code}
$(Monad.concatMapM Mappable.mkPassN [2 .. 7 :: Natural])
\end{code}

\begin{code}
$(Monad.concatMapM Mappable.mkOnN [2 .. 7 :: Natural])
\end{code}

\begin{spec}
type family MappableTypes t

type instance (Functor f, MappableTypes t) => type instance MappableTypes (f t)
\end{spec}

\begin{spec}
class NestedMap a b s t where
  (<$$>) :: (a -> b) -> s -> t

instance {-# OVERLAPPING #-} Functor f => NestedMap a b (f a) (f b) where
  (<$$>) = fmap

instance {-# OVERLAPPABLE #-} (NestedMap a b s t, Functor f) => NestedMap a b (f s) (f t) where
  f <$$> x = fmap (f <$$>) x

double :: NestedMap Integer Integer s s => s -> s
double = ((* (2 :: Integer)) <$$>)

example :: Maybe [Maybe (Either String Integer)]
example = double (Just [Nothing, Just (Left "hi"), Just (Right 42)])
\end{spec}

\begin{spec}
class Mappable (functors :: [Type -> Type]) where
  (<$$>) :: (base -> base') -> List.Foldl Base.Apply base functors
                            -> List.Foldl Base.Apply base' functors
\end{spec}

\begin{spec}
instance Functor functor => Mappable functor base where
  (<$$>) = fmap
\end{spec}
\printbibliography
\end{document}
