||| Simple GADTs for F#
module Sg4f

%default total
%access public export

mutual
  ||| A term in the language
  ||| arity Z - monovalue
  ||| arity (S n) - function
  ||| universe 0 - values
  ||| universe 1 - types
  ||| universe 2 - kinds
  ||| universe 2 - sorts
  data Term : (arity : Nat) -> (universe : Nat) -> Type where
    ||| A named term
    NamedTerm : Name n u -> Term n u
    ||| Function application
    Appl : Term (S n) u -> Term m u -> Term n u
    ||| Type constructor operator. Its terms cannot be values.
    Arrow : Term n (S u) -> Term m (S u) -> Term (S m) (S u)

  ||| An actual name of a term
  data Name : (arity : Nat) -> (universe : Nat) -> Type where
    ||| The name of Type in any universe starting with 2 (since the lowest Type
    ||| has as its type Kind).
    Tau : Name 0 (S (S n))
    ||| A primitive type or type constructor in universe one, opaque to the
    ||| source language because taken for granted as existing in the target
    ||| language. Syntax:
    |||   primitive string : Type
    |||   primitive Maybe : Type -> Type
    |||   primitive Either : Type -> Type -> Type
    ||| The term in universe two is the type of the primitive: all primitives
    ||| have a type of Type or of some type constructor, which are kinds, so it
    ||| is in universe two.
    PrimType : String -> Term n 2 -> Name n 1

||| Get the name of the type or type constructor
typeName : Name n u -> String
typeName {n=Z} {u = (S (S Z))} Tau = "Type"
typeName {n=Z} {u = (S (S (S Z)))} Tau = "Kind"
typeName {n=Z} {u = (S (S (S (S Z))))} Tau = "Sort"
typeName {n=Z} {u = (S (S (S (S (S _)))))} Tau = "Why asketh thou such things?"
typeName (PrimType x _) = x

||| Get the type of some type variable. Returns a term in the next unvierse up,
||| with the arity reset.
getTypeOfName : Name n u -> Term n (S u)
getTypeOfName Tau = NamedTerm Tau
getTypeOfName (PrimType _ t) = ?zugdu

||| Get the arity of the type of the term
ArityOfType : Term n u -> Nat
ArityOfType {n} {u} (NamedTerm x) = n
ArityOfType (Appl x y) = ?ArityOfType_rhs_2
ArityOfType (Arrow x y) = ?ArityOfType_rhs_3

||| Get the type of some term. Returns a term in the next unvierse up.
getType : (t : Term n u) -> Term Z (ArityOfType t)
getType (NamedTerm x) = ?getType_rhs_1
getType (Appl x y) = ?getType_rhs_2
getType (Arrow x y) = ?getType_rhs_3
