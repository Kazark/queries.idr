module Three3

%default total
%access public export

data Qry : (Type -> Type) -> Type -> Type where
  ||| Pure for monad/applicative: lift a plain value into the tree
  Pure : a -> Qry q a
  ||| Lift a query into the tree
  Lift : q i -> (i -> a) -> Qry q a
  ||| Gives us a monoid operation
  Join : Qry q (Qry q a) -> Qry q a

liftQ : q a -> Qry q a
liftQ qry = Lift qry id

--infixr 5 ^+^
--||| Generalized semigroup operation, not requiring anything from the underlying
--||| data types
--(^+^) : Qry q a -> Qry q b -> Qry q (a, b)
--(Pure x) ^+^ r = ?bat_2
--(Lift q h) ^+^ r = ?bat_3
--(Join qry) ^+^ r = ?bat_4

-- Back to the same old problem. Must surface the size in the type to
-- demonstrate well-foundedness. Will then loose monad and applicative
-- instances...
Functor (Qry q) where
  map f (Pure x) = Pure $ f x
  map f (Lift q h) = ?functor_huh_2
  map f (Join q) = Join $ map (map f) q
