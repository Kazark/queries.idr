module FreeQ

%default total
%access public export

||| A tree structure for combining queries, perhaps slightly less expressive
||| than a free monad, but easier to prove total, etc. I say less expressive,
||| because I do not believe it is a monad, whereas my applicative instance
||| seems pretty solid. Moreover, it has a nice monoid instance, given a monoid
||| on the type it is parameterized over (but requiring no effort from the query
||| GADT). I have also provided a generalized semigroup operation based on
||| pairing items together. This seems promising as something very useful for
||| DSLs. Now, how do we make use of it in F#?!?
data QryTree : (Type -> Type) -> Type -> Type where
  ||| Pure for monad/applicative: lift a plain value into the tree
  PureLeaf : a -> QryTree q a
  ||| Lift a query into the tree
  LiftLeaf : q i -> (i -> a) -> QryTree q a
  ||| Gives us a monoid operation
  Branch : QryTree q a -> QryTree q b -> ((a, b) -> c) -> QryTree q c

infixr 5 ^+^

||| Generalized semigroup operation
(^+^) : QryTree q a -> QryTree q b -> QryTree q (a, b)
q ^+^ r = Branch q r id

Semigroup a => Semigroup (QryTree q a) where
  q <+> r = Branch q r (uncurry (<+>))

Monoid a => Monoid (QryTree q a) where
  neutral = PureLeaf neutral

Functor q => Functor (QryTree q) where
  map f (PureLeaf x) = PureLeaf (f x)
  map f (LiftLeaf q handle) = LiftLeaf q (f . handle)
  map f (Branch q r handle) = Branch q r (f . handle)

||| The s combinator, with a dash of uncurrying
s' : (a -> (b -> c)) -> (d -> b) -> (a, d) -> c
s' f g (x, y) = f x (g y)

||| I am not any good at equality proofs in Idris. However, I am not content to
||| rest uncertain about whether this applicative instance is lawful! So here
||| you go: back to geometry class: a long-hand proof, in the comments!
|||
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
|||   -> QED
|||
||| composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
|||   PureLeaf (.) <*> u <*> v <*> w = u <*> (v <*> w)
|||   PureLeaf (\f g x => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w)
|||   | PureLeaf (.) <*> PureLeaf u' <*> v <*> w = PureLeaf u' <*> (v <*> w)
|||     | PureLeaf (u' .) <*> PureLeaf v' <*> w = PureLeaf u' <*> (PureLeaf v' <*> w)
|||       -> PureLeaf (u' . v') <*> w = PureLeaf u' <*> (PureLeaf v' <*> w)
|||          | PureLeaf (\x => u' (v' x)) <*> PureLeaf w' = PureLeaf u' <*> (PureLeaf v' <*> PureLeaf w')
|||            -> PureLeaf (u' (v' w')) = PureLeaf u' <*> PureLeaf (v' w')
|||            -> PureLeaf (u' (v' w')) = PureLeaf (u' (v' w'))
|||            -> QED
|||          | PureLeaf (u' . v') <*> LiftLeaf q w' = PureLeaf u' <*> (PureLeaf v' <*> LiftLeaf q w')
|||            -> LiftLeaf q ((u' . v') . w') = PureLeaf u' <*> (LiftLeaf q (v' . w'))
|||            -> LiftLeaf q (u' . (v' . w')) = LiftLeaf q (u' . (v' . w'))
|||            -> QED
|||          | PureLeaf (u' . v') <*> Branch q r w' = PureLeaf u' <*> (PureLeaf v' <*> Branch q r w')
|||            -> Branch q r ((u' . v') . w') = PureLeaf u' <*> (Branch q r (v' . w'))
|||            -> Branch q r (u' . (v' . w')) = Branch q r (u' . (v' . w'))
|||            -> QED
|||       -> QED
|||     | PureLeaf (u' .) <*> LiftLeaf q v' <*> w = PureLeaf u' <*> (LiftLeaf q v' <*> w)
|||       -> LiftLeaf q ((u' .) . v') <*> w = PureLeaf u' <*> (LiftLeaf q v' <*> w)
|||       -> LiftLeaf q ((\g x => u' (g x)) . v') <*> w = PureLeaf u' <*> (LiftLeaf q v' <*> w)
|||       -> LiftLeaf q (\y => (\g x => u' (g x)) (v' y)) <*> w = PureLeaf u' <*> (LiftLeaf q v' <*> w)
|||       -> LiftLeaf q (\y x => u' (v' y x)) <*> w = PureLeaf u' <*> (LiftLeaf q v' <*> w)
|||          | LiftLeaf q (\y x => u' (v' y x)) <*> PureLeaf w' = PureLeaf u' <*> (LiftLeaf q v' <*> PureLeaf w')
|||            -> LiftLeaf q (\z => (\y x => u' (v' y x)) z w') = PureLeaf u' <*> (LiftLeaf q (\y => v' y w'))
|||            -> LiftLeaf q (\z => (\x => u' (v' z x)) w') = LiftLeaf q (\z => u' ((\y => v' y w') z))
|||            -> LiftLeaf q (\z => u' (v' z w')) = LiftLeaf q (\z => u' (v' z w'))
|||            -> QED
|||          | LiftLeaf q (\y x => u' (v' y x)) <*> LiftLeaf r w' = PureLeaf u' <*> (LiftLeaf q v' <*> LiftLeaf r w')
|||            -> Brand (LiftLeaf q id) (LiftLeaf r id) (s' (\y x => u' (v' y x)) w') = PureLeaf u' <*> (Branch (LiftLeaf q id) (LiftLeaf r id) (s' v' w'))
|||            -> Brand (LiftLeaf q id) (LiftLeaf r id)  (\(a, b) => (\y x => u' (v' y x)) a (w' b)) = Branch (LiftLeaf q id) (LiftLeaf r id)  (u' . s' v' w')
|||            -> ... (\(a, b) => (\x => u' (v' a x)) (w' b)) = ... (u' . s' v' w')
|||            -> ... (\(a, b) => u' (v' a (w' b))) = ... (u' . s' v' w')
|||            -> ... (\(a, b) => u' (s' v' w' (a, b))) = ... (u' . s' v' w')
|||            -> ... (\(a, b) => (u' . s' v' w') (a, b)) = ... (u' . s' v' w')
|||            -> ... (u' . s' v' w') = ... (u' . s' v' w')
|||            -> QED
|||          | LiftLeaf q (\y x => u' (v' y x)) <*> Branch r s w' = PureLeaf u' <*> (LiftLeaf q v' <*> Branch r s w')
|||            -> Brand (LiftLeaf q id) (Breanch r s id) (s' (\y x => u' (v' y x)) w') = PureLeaf u' <*> (Branch (LiftLeaf q id) (Breanch r s id) (s' v' w'))
|||            -> Brand (LiftLeaf q id) (Breanch r s id)  (\(a, b) => (\y x => u' (v' y x)) a (w' b)) = Branch (LiftLeaf q id) (Breanch r s id)  (u' . s' v' w')
|||            -> ... (\(a, b) => (\x => u' (v' a x)) (w' b)) = ... (u' . s' v' w')
|||            -> ... (\(a, b) => u' (v' a (w' b))) = ... (u' . s' v' w')
|||            -> ... (\(a, b) => u' (s' v' w' (a, b))) = ... (u' . s' v' w')
|||            -> ... (\(a, b) => (u' . s' v' w') (a, b)) = ... (u' . s' v' w')
|||            -> ... (u' . s' v' w') = ... (u' . s' v' w')
|||            -> QED
|||       -> QED
||| Suddenly I do the math and realized that I'm only 2/9th's done... perhaps
||| there is a better way to approach this than doing it late at night. The
||| results so far are very promising in that it seems that the same laborious
||| technique should continue to work. Perhaps this could be reduced more easily
||| by introducing some lemmas. Or by figuring out how to do it with Idris. Or
||| by researching if it has been done before. Or one could argue this way: we
||| have at this point really encountered all the scenarios. Things work right
||| if pure comes before, or after; it cancels out. LiftLeaf and Branch
||| fundamentally have the same semanticcs, and the proof above regarding the
||| semantics of the S-combinator seem conclusive for all cases involving them.
||| It seems that for a proof of this length, it is foolhardy to continue
||| without computer assistance and checking. My sense that this is not a bogus
||| implementation of applicative is quite high at this point. I leave it as an
||| exercise for the reader to complete, where by "the reader" I mean "me, I
||| hope, at some later date."
|||
||| homomorphism: pure f <*> pure x = pure (f x)
|||   PureLeaf f <*> PureLeaf x = PureLeaf (f x)
|||   -> QED
|||
||| interchange: u <*> pure y = pure ($ y) <*> u
|||   u <*> PureLeaf y = PureLeaf ($ y) <*> u
|||   | PureLeaf f <*> PureLeaf y = PureLeaf ($ y) <*> PureLeaf f
|||     -> PureLeaf (f y) = PureLeaf (f $ y)
|||     -> PureLeaf (f y) = PureLeaf (f y)
|||     -> QED
|||   | LiftLeaf q f <*> PureLeaf y = PureLeaf ($ y) <*> LiftLeaf q f
|||     -> LiftLeaf q f <*> PureLeaf y = PureLeaf ($ y) <*> LiftLeaf q f
|||     -> LiftLeaf q (\z => f z y) = LiftLeaf q ((\x => \g => g x) y . f)
|||     -> LiftLeaf q (\z => f z y) = LiftLeaf q ((\g => g y) . f)
|||     -> LiftLeaf q (\z => f z y) = LiftLeaf q (\z => (\g => g y) (f z))
|||     -> LiftLeaf q (\z => f z y) = LiftLeaf q (\z => f z y)
|||     -> QED
|||   | Branch q r f <*> PureLeaf y = PureLeaf ($ y) <*> Branch q r f
|||     -> Branch q r f <*> PureLeaf y = PureLeaf ($ y) <*> Branch q r f
|||     -> Branch q r (\z => f z y) = Branch q r ((\x => \g => g x) y . f)
|||     -> Branch q r (\z => f z y) = Branch q r ((\g => g y) . f)
|||     -> Branch q r (\z => f z y) = Branch q r (\z => (\g => g y) (f z))
|||     -> Branch q r (\z => f z y) = Branch q r (\z => f z y)
|||     -> QED
|||   -> QED
|||
||| These are the four properties I found needful to prove based on my
||| understanding of Haskell's Control.Applicative documentation.
Functor q => Applicative (QryTree q) where
  pure = PureLeaf
  (PureLeaf f) <*> (PureLeaf x) =
    PureLeaf (f x)
  (PureLeaf f) <*> (LiftLeaf q g) =
    LiftLeaf q (f . g)
  (PureLeaf f) <*> (Branch q r g) =
    Branch q r (f . g)
  (LiftLeaf q f) <*> (PureLeaf x) =
    LiftLeaf q (\y => f y x)
  (LiftLeaf q f) <*> (LiftLeaf r g) =
    Branch (LiftLeaf q id) (LiftLeaf r id) $ s' f g
  (LiftLeaf q f) <*> (Branch r s g) =
    Branch (LiftLeaf q id) (Branch r s id) $ s' f g
  (Branch q r f) <*> (PureLeaf x) =
    Branch q r (\y => f y x)
  (Branch q r f) <*> (LiftLeaf s g) =
    Branch (Branch q r id) (LiftLeaf s id) $ s' f g
  (Branch q r f) <*> (Branch s t g) =
    Branch (Branch q r id) (Branch s t id) $ s' f g

-- How would you implement a monad?
-- Functor q => Monad (QryTree q) where
-- The first case would be easy:
--   (PureLeaf x) >>= f = f x
-- However, wouldn't you get stuck on these?
--   (LiftLeaf x g) >>= f = ?monads_yikes_2
--   (Branch x y g) >>= f = ?monads_yikes_3
-- It seems that we have insufficient power to smash down the results, since we
-- cannot actually produce the tree from f in these cases, without introducing
-- another lambda abstraction: but if we do that, we have to wrap it in a tree:
-- but then, inside the lambda abstraction, we cannot destroy the tree that we
-- got out of the f; I take this as a proof that there is no monad instance.
