module TreeQ2

%default total
%access public export

data Qry : (Type -> Type) -> Type -> Type where
  ||| Pure for monad/applicative: lift a plain value into the tree
  Pure : a -> Qry q a
  ||| Lift a query into the tree
  Lift : q i -> (i -> a) -> Qry q a
  ||| Gives us a monoid operation
  Attach : Qry q a -> q i -> ((a, i) -> b) -> Qry q b

liftQ : q a -> Qry q a
liftQ qry = Lift qry id

infixr 5 ^+^

||| Generalized semigroup operation. Not nearly as simple as the tree version.
||| This does not bode well. Moreover, one wonders what all this extra wrapping
||| will do to F# if translated to it...
(^+^) : Qry q a -> Qry q b -> Qry q (a, b)
(Pure x) ^+^ (Pure y) = Pure (x, y)
(Lift q h) ^+^ (Pure x) = Lift q (\y => (h y, x))
(Attach q r h) ^+^ (Pure x) = Attach q r (\y => (h y, x))
(Pure x) ^+^ (Lift q h) = Lift q (\y => (x, h y))
(Lift q h) ^+^ (Lift r i) = Attach (Lift q h) r (\(x, y) => (x, i y))
(Attach q r h) ^+^ (Lift s i) = Attach (Attach q r h) s (\(x, y) => (x, i y))
(Pure x) ^+^ (Attach q r h) = Attach q r (\y => (x, h y))
(Lift q h) ^+^ (Attach s r i) =
  Attach (Attach s q id) r (\((b, a), c) => (h a, i (b, c)))
(Attach q r h) ^+^ (Attach s t i) =
  Attach (Attach (q ^+^ s) r id) t (\(((a, c), b), d) => (h (a, b), i (c, d)))

||| TODO Now I'm not sure I'm at all careful enough in my implementation. I may
||| accidentally be assuming commutivity of the underlying semigroup.
Semigroup a => Semigroup (Qry q a) where
  (Pure y) <+> (Pure x) = Pure (x <+> y)
  (Lift y f) <+> (Pure x) = Lift y ((<+> x) . f)
  (Attach y z f) <+> (Pure x) = Attach y z ((<+> x) . f)
  (Pure y) <+> (Lift x f) = Lift x ((<+> y) . f)
  (Lift y g) <+> (Lift x f) = Attach (Lift y g) x (uncurry (<+>) . map f)
  (Attach y z g) <+> (Lift x f) =
    Attach (Attach y z g) x (\(a, b) => a <+> f b)
  (Pure z) <+> (Attach x y f) = Attach x y ((<+> z) . f)
  (Lift z g) <+> (Attach x y f) =
    Attach (Attach x y f) z (\(a, b) => a <+> g b)
  (Attach z w g) <+> (Attach x y f) = ?semigroup_huh_6

-- Augh I give up this is madness. If I were to succeed, I can't even imagine
-- how hard it would be to prove this all correct or translate it into anything
-- in F#.
