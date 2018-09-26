||| http://okmij.org/ftp/Computation/free-monad.html
module Freer

%default total
%access public export

data FFree : (Type -> Type) -> Nat -> Type -> Type where
  FPure   : a -> FFree g n a
  FImpure : g x -> (x -> FFree g n a) -> FFree g (S n) a

Functor (FFree g n) where
  map f (FPure x)     = FPure (f x)
  map f (FImpure u q) = FImpure u (map f . q)

pure : a -> FFree g n a
pure = FPure

promote : {m : Nat} -> FFree g n a -> FFree g (n + m) a
promote (FPure x)     = FPure x
promote (FImpure u q) = FImpure u (promote . q)

assocS : (m : Nat) -> (n : Nat) -> m + S n = S (m + n)
assocS Z n = Refl
assocS (S m) n = cong $ assocS m n

apply : FFree g n (a -> b) -> FFree g m a -> FFree g (m + n) b
apply {n} {m} (FPure f) x =
  promote $ map f x
apply {n=S n} {m} (FImpure u q) x =
  let y = flip apply x . q
  in rewrite assocS m n in FImpure u y

bind : (a -> FFree g n b) -> FFree g m a -> FFree g (n + m) b
bind {n} {m} f (FPure x) = promote $ f x
bind {n} {m=S m} f (FImpure u f') =
  let y = bind f . f'
  in rewrite assocS n m in FImpure u y

join : FFree g m (FFree g n a) -> FFree g (n + m) a
join = bind id

--Applicative (FFree g) where
--  pure = FPure
--
--infixr 5 >=>
--
--(>=>) : Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
--f >=> g = (>>= g) . f
--
--Monad (FFree g) where
--  (FPure x) >>= f = f x
--  (FImpure u f') >>= f = FImpure u (f' >=> f)
