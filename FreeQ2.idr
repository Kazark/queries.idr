module FreeQ2

%default total
%access public export

||| Type representing a query type which encodes a query _request_ (presumably a
||| GADT), paired with a handler for it. The handler's output type is
||| parameterized over a size to help smooth out totality proofs when used with
||| the free query. This makes us loose our functor instance, but we can still
||| define a concept of map.
record HandledQry (q : Type -> Type) (n : Nat) (o : Nat -> Type) where
  constructor HandleQry
  qry : q i
  handle : i -> o n

mapHQ : {n, m : Nat} -> (a n -> b m) -> HandledQry q n a -> HandledQry q m b
mapHQ f (HandleQry qry handle) = HandleQry qry (f . handle)

||| Since the standard Haskell-style Free monad is not strictly positive, and I
||| do not understand yet how to constrain a functor to be strictly positive;
||| nor do I understand Conor McBride's `General` free monad in
||| [Turing-Completeness Totally
||| Free](https://pdfs.semanticscholar.org/e291/5b546b9039a8cf8f28e0b814f6502630239f.pdf)
||| I define a FreeQ: a version of free that is monomorphic to the concept of a
||| handled query---that is, of a query GADT paired with a handler
||| function---but not monorphic to the specific query GADT. This definition is
||| then strictly positive. With the addition of a size to the type, the
||| consuming code is able to be total. Thus I am able to get one definition of
||| free for all my query DSLs, which is everywhere to date that I have
||| personally had a need for free monads, and yet maintain my dogmatism about
||| total programming. I don't doubt that sometime in the future I will have a
||| need for free monads with something that is not a query. But let the future
||| be the future. For now, it would be a tremendous step forward in my F# code
||| if I could use this approach!
data FreeQ : Nat -> (Type -> Type) -> Type -> Type where
  PureQ : a -> FreeQ Z q a
  BindHQ : HandledQry q n (\m => FreeQ m q a)
         -> FreeQ (S n) q a

||| Thankfully due to the nature of functor, we are ablel to implement the
||| interface, since it does not change the size of our FreeQ.
Functor (FreeQ n q) where
  map f (PureQ x) = PureQ (f x)
  map f (BindHQ slave) = BindHQ (mapHQ (map f) slave)

||| Recover applicative and monad instances by lifting... I mean half the point
||| of a free monad is to actually be able to use do notation etc. right?
record FreeQry (q : Type -> Type) a where
  constructor WrapFHQ
  unwrapFHQ : FreeQ qsize q a

Functor (FreeQry q) where
  map f (WrapFHQ x) = WrapFHQ $ map f x

||| Applicative apply, except we can't implement the type class because the size
||| of our type changes between inputs and output.
apfq : FreeQ n f (a -> b) -> FreeQ m f a -> FreeQ (n + m) f b
apfq {n=Z} (PureQ y) x = map y x
apfq (BindHQ y) x = BindHQ (mapHQ (flip apfq x) y)

Applicative (FreeQry q) where
  pure x = WrapFHQ (PureQ x)
  (WrapFHQ f) <*> (WrapFHQ x) = WrapFHQ $ apfq f x

||| Monad bind, except we can't implement the type class because the size of our
||| type changes between inputs and output.
bindfq : Functor f => (a -> FreeQ n f b) -> FreeQ m f a -> FreeQ (m + n) f b
bindfq {n} {m=Z} f (PureQ x) = f x
bindfq f (BindHQ x) = BindHQ (mapHQ (bindfq f) x)

||| Monad join, except we can't implement the type class because the size of our
||| type changes between inputs and output.
joinfq : Functor f => FreeQ n f (FreeQ m f a) -> FreeQ (n + m) f a
joinfq (PureQ x) = x
joinfq (BindHQ x) = BindHQ (mapHQ joinfq x)

join' : (n : Nat) -> FreeQ n q (FreeQry q a) -> FreeQry q a
join' Z (PureQ x) = x
join' (S m) (BindHQ x) =
  ?asdf $ map (join' m) x
  --WrapFHQ (S m) $ BindHQ $ map (unwrapFHQ . join' m) x

Monad (FreeQry q) where
  join (WrapFHQ n x) = join' n x
