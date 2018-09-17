module FreeQ

%default total
%access public export

data QryTree : (Type -> Type) -> Type -> Type where
  ||| Pure for monad/applicative: lift a plain value into the tree
  PureLeaf : a -> QryTree q a
  ||| Lift a query into the tree
  LiftLeaf : q i -> (i -> a) -> QryTree q a
  ||| Gives us a monoid operation
  Branch : QryTree q a -> QryTree q b -> ((a, b) -> c) -> QryTree q c

Functor q => Functor (QryTree q) where
  map f (PureLeaf x) = PureLeaf (f x)
  map f (LiftLeaf q handle) = LiftLeaf q (f . handle)
  map f (Branch q r handle) = Branch q r (f . handle)

||| identity: pure id <*> v = v
|||   PureLeaf id <*> v = v
|||   | PureLeaf id <*> PureLeaf x = v
|||     -> PureLeaf (id x) = v
|||     -> PureLeaf x = v
|||     -> v = v
|||     -> QED
|||   | PureLeaf id <*> LiftLeaf q g = v
|||     -> LiftLeaf q (id . g) = v
|||     -> LiftLeaf q g = v
|||     -> v = v
|||     -> QED
|||   | PureLeaf id <*> Branch q r g = v
|||     -> Branch q r (id . g) = v
|||     -> Branch q r g = v
|||     -> v = v
|||     -> QED
||| composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
||| homomorphism: pure f <*> pure x = pure (f x)
||| interchange: u <*> pure y = pure ($ y) <*> u
Functor q => Applicative (QryTree q) where
  pure = PureLeaf
  (PureLeaf f) <*> (PureLeaf x) = PureLeaf (f x)
  (PureLeaf f) <*> (LiftLeaf q g) = LiftLeaf q (f . g)
  (PureLeaf f) <*> (Branch q r g) = Branch q r (f . g)
  (LiftLeaf q f) <*> (PureLeaf x) = LiftLeaf q (\y => f y x)
  (LiftLeaf q f) <*> (LiftLeaf r g) = ?apqt_4
  (LiftLeaf q f) <*> (Branch r s g) = ?apqt_5
  (Branch q r f) <*> (PureLeaf x) = Branch q r (\y => f y x)
  (Branch q r f) <*> (LiftLeaf s g) = ?apqt_6
  (Branch q r f) <*> (Branch s t g) = ?apqt_7
