module Free

%default total
%access public export

-- BEWARE: many assert_total's in this code. Not because I believe in using them
-- in anything but primitive code or FFI interface, but just because I am trying
-- to learn more about free monads for use in F#, where I would drool for a
-- compiler complaint about totality

data Free : (Type -> Type) -> Type -> Type where
  Pure : a -> Free f a
  Bind : f (Free f a) -> Free f a

partial
pMap : Functor f => (a -> b) -> Free f a -> Free f b
pMap f (Pure x) = Pure (f x)
pMap f (Bind slave) = Bind (map (pMap f) slave)

Functor f => Functor (Free f) where
  map f x = assert_total $ pMap f x

partial
ap : Functor f => Free f (a -> b) -> Free f a -> Free f b
ap (Pure y) x = map y x
ap (Bind y) x = Bind (map (flip ap x) y)

Functor f => Applicative (Free f) where
  pure = Pure
  f <*> x = assert_total $ ap f x

partial
bind : Functor f => (a -> Free f b) -> Free f a -> Free f b
bind f (Pure x) = f x
bind f (Bind x) = Bind (map (bind f) x)

Functor f => Monad (Free f) where
  x >>= f = assert_total $ bind f x

B : Functor f => f (Free f a) -> Free f a
B x = assert_total $ Bind x

data Qry : Type -> Type where
  LsFiles : (List String -> a) -> String -> Qry a
  ReadText : (String -> a) -> String -> Qry a
  DirExists : (Bool -> a) -> String -> Qry a

data Cmd
  = WriteLines String (List String)
  | CreateDir String
  | DeleteFile String
  | DeleteDir String

Functor Qry where
  map f (LsFiles g x) = LsFiles (f . g) x
  map f (ReadText g x) = ReadText (f . g) x
  map f (DirExists g x) = DirExists (f . g) x

traverse : Functor f => (a -> Free f b) -> List a -> Free f (List b)
traverse f [] = pure List.Nil
traverse f (x::xs) = [| List.(::) (f x) (traverse f xs) |]

liftQry : Qry a -> Free Qry a
liftQry x = B (map Pure x)

lsFiles : String -> Free Qry (List String)
lsFiles = liftQry . LsFiles id

readText : String -> Free Qry String
readText = liftQry . ReadText id

lmap : (a -> b) -> List a -> List b
lmap f [] = []
lmap f (x :: xs) = f x :: lmap f xs

consolidate : String -> String -> Free Qry (List Cmd)
consolidate frum tu = do
  files <- lsFiles frum
  texts <- traverse readText files
  pure $ lmap DeleteFile files ++ [DeleteDir frum, CreateDir tu, WriteLines (tu ++ "/" ++ "consolidated.txt") texts]
