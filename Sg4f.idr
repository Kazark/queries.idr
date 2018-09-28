||| Simple GADTs for F#
module Sg4f

%default total
%access public export

mutual
  ||| A term in the language
  ||| universe 0 - values
  ||| universe 1 - types
  ||| universe 2 - kinds
  ||| universe 2 - sorts
  data Term : (universe : Nat) -> Type where
    ||| A named term
    NamedTerm : Name u -> Term u
    ||| Function application
    Appl : (f : Func u) -> (a : Term u) {- -> {auto prf : getInputType f = getType a} -} -> Term u
    ||| Type constructor operator. Its terms cannot be values.
    Arrow : Term (S u) -> Term (S u) -> Term (S u)
    ||| Func is parameterized by the type of its input; thus, we must go down a
    ||| universe from its input to get its universe
    FunTerm : Func u -> Term u

  data Func : (u : Nat) -> Type where
    ||| The input and output type of the constructor
    Ctr : Term (S u) -> Term (S u) -> Func u

  ||| An actual name of a term
  data Name : (universe : Nat) -> Type where
    ||| The name of Type in any universe starting with 2 (since the lowest Type
    ||| has as its type Kind).
    Tau : Name (S (S n))
    ||| A primitive type or type constructor in universe one, opaque to the
    ||| source language because taken for granted as existing in the target
    ||| language. Syntax:
    |||   primitive string : Type
    |||   primitive Maybe : Type -> Type
    |||   primitive Either : Type -> Type -> Type
    ||| The term in universe two is the type of the primitive: all primitives
    ||| have a type of Type or of some type constructor, which are kinds, so it
    ||| is in universe two.
    PrimType : String -> Term 2 -> Name 1

  ||| Get the type of some term. Returns a term in the next unvierse up.
  getType : Term u -> Term (S u)
  getType (NamedTerm Tau) = NamedTerm Tau
  getType (NamedTerm (PrimType _ t)) = t
  getType (Appl (Ctr _ z) _) = z
  getType (Arrow x y) = NamedTerm Tau
  getType (FunTerm (Ctr t x)) = Arrow t x

||| Get the name of the type or type constructor
typeName : Name u -> String
typeName {u = (S (S Z))} Tau = "Type"
typeName {u = (S (S (S Z)))} Tau = "Kind"
typeName {u = (S (S (S (S Z))))} Tau = "Sort"
typeName {u = (S (S (S (S (S _)))))} Tau = "Why asketh thou such things?"
typeName (PrimType x _) = x
