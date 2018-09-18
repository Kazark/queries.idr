module Crazy

%default total
%access public export

data QVect : (Type -> Type) -> List Type -> Type where
  Nil : QVect q []
  (::) : q x -> QVect q xs -> QVect q (x :: xs)

||| Type representing a query type which encodes a query _request_ (presumably a
||| GADT), paired with a handler for it.
record HandledQry (q : Type -> Type)  (a : Type) where
  constructor HandleQry
  qry : q i
  handle : i -> a

record Qry (q : Type -> Type) (a : Type) where
  constructor Q
  queries : QVect (HandledQry q) ts
  handleN : QVect Basics.id ts -> a

pure : a -> Qry q a
pure x = Q [] (\_ => x)
