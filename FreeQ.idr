module FreeQ

%default total
%access public export

||| Type representing a query type which encodes a query _request_ (presumably a
||| GADT), paired with a handler for it.
record HandledQry (q : Type -> Type) (a : Type) where
  constructor HandleQry
  qry : q z
  handle : z -> a

||| HandledQry q is a strictly positive functor, regardless of the shape of q!
Functor (HandledQry q) where
  map f (HandleQry qry handle) = HandleQry qry (f . handle)

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
  PureQ : a -> FreeQ Z f a
  BindHQ : HandledQry q (FreeQ n (HandledQry q) a)
         -> FreeQ (S n) (HandledQry q) a

||| Thankfully due to the nature of functor, we are ablel to implement the
||| interface, since it does not change the size of our FreeQ.
Functor f => Functor (FreeQ n f) where
  map f (PureQ x) = PureQ (f x)
  map f (BindHQ slave) = BindHQ (map (map f) slave)

size : FreeQ n f a -> Nat
size {n} _ = n

||| Recover applicative and monad instances by lifting... I mean half the point
||| of a free monad is to actually be able to use do notation etc. right?
record FreeQry (q : Type -> Type) a where
  constructor WrapFHQ
  unwrapFHQ : FreeQ n (HandledQry q) a

Functor (FreeQry q) where
  map f (WrapFHQ x) = WrapFHQ $ map f x

||| Applicative apply, except we can't implement the type class because the size
||| of our type changes between inputs and output.
apfq : Functor f => FreeQ n f (a -> b) -> FreeQ m f a -> FreeQ (n + m) f b
apfq {n=Z} (PureQ y) x = map y x
apfq (BindHQ y) x = BindHQ (map (flip apfq x) y)

Applicative (FreeQry q) where
  pure x = WrapFHQ (PureQ x)
  (WrapFHQ f) <*> (WrapFHQ x) = WrapFHQ $ apfq f x

||| Monad bind, except we can't implement the type class because the size of our
||| type changes between inputs and output.
bindfq : Functor f => (a -> FreeQ n f b) -> FreeQ m f a -> FreeQ (m + n) f b
bindfq {n} {m=Z} f (PureQ x) = f x
bindfq f (BindHQ x) = BindHQ (map (bindfq f) x)

||| Monad join, except we can't implement the type class because the size of our
||| type changes between inputs and output.
joinfq : Functor f => FreeQ n f (FreeQ m f a) -> FreeQ (n + m) f a
joinfq (PureQ x) = x
joinfq (BindHQ x) = BindHQ (map joinfq x)

linkashorn : FreeQ n (HandledQry q) (FreeQry q a) -> FreeQry q a
linkashorn (PureQ x) = x
linkashorn (BindHQ x) = WrapFHQ $ BindHQ $ map (unwrapFHQ . linkashorn) x

Monad (FreeQry q) where
  join (WrapFHQ x) = linkashorn x

||| Example specific query GADT
data FSQry : Type -> Type where
  LsFiles : String -> FSQry (List String)
  ReadText : String -> FSQry String
  DirExists : String -> FSQry Bool

||| Example accompanying commands, to in conjunction with the FSQry, form a sort
||| of little filesystem DSL.
data FSCmd
  = WriteLines String (List String)
  | CreateDir String
  | DeleteFile String
  | DeleteDir String

--B : Functor f => f (FreeQ f a) -> FreeQ f a
--B x = assert_total $ BindHQ x
--
--traverse : Functor f => (a -> FreeQ f b) -> List a -> FreeQ f (List b)
--traverse f [] = pure List.Nil
--traverse f (x::xs) = [| List.(::) (f x) (traverse f xs) |]
--
--liftQry : Qry a -> FreeQ Qry a
--liftQry x = B (map PureQx)
--
--lsFiles : String -> FreeQ Qry (List String)
--lsFiles = liftQry . LsFiles id
--
--readText : String -> FreeQ Qry String
--readText = liftQry . ReadText id
--
--lmap : (a -> b) -> List a -> List b
--lmap f [] = []
--lmap f (x :: xs) = f x :: lmap f xs
--
--consolidate : String -> String -> FreeQ Qry (List Cmd)
--consolidate frum tu = do
--  files <- lsFiles frum
--  texts <- traverse readText files
--  pure $ lmap DeleteFile files ++ [DeleteDir frum, CreateDir tu, WriteLines (tu ++ "/" ++ "consolidated.txt") texts]
