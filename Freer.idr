||| http://okmij.org/ftp/Computation/free-monad.html
module Freer

%default total
%access public export

||| Argh, has the same totality problems as free monad!
data FFree : (Type -> Type) -> Type -> Type where
  FPure   : a -> FFree g a
  FImpure : g x -> (x -> FFree g a) -> FFree g a

fmap : (a -> b) -> FFree g a -> FFree g b
fmap f (FPure x)     = FPure (f x)
fmap f (FImpure u q) = FImpure u (fmap f . q)

Functor (FFree g) where
  map f (FPure x)     = FPure (f x)
  map f (FImpure u q) = FImpure u (map f . q)

Applicative (FFree g) where
  pure = FPure
  (FPure f) <*> x = map f x
  (FImpure u q) <*> x = FImpure u ((<*> x) . q)

infixr 5 >=>

(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
f >=> g = (>>= g) . f

Monad (FFree g) where
  (FPure x) >>= f = f x
  (FImpure u f') >>= f = FImpure u (f' >=> f)
