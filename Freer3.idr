||| http://okmij.org/ftp/Computation/free-monad.html
||| https://pdfs.semanticscholar.org/e291/5b546b9039a8cf8f28e0b814f6502630239f.pdf
module Freer

%default total
%access public export

data Freer : (s : Type) -> (s -> Type) -> Type -> Type where
  Pure   : x -> Freer s t x
  Impure : (a : s) -> (t a -> Freer s t x) -> Freer s t x

||| Catamorphism
fold : (x -> y) -> ((a : s) -> (t a -> y) -> y) -> Freer s t x -> y
fold r _ (Pure x) = r x
fold r c (Impure s k) = c s $ \t => fold r c (k t)

bind : (x -> Freer s t y) -> Freer s t x -> Freer s t y
bind k = fold k Impure

call : (a : s) -> Freer s t (t a)
call a = Impure a Pure

Functor (Freer s t) where
  map f = bind (Pure . f)

Applicative (Freer s t) where
  pure = Pure
  (Pure f) <*> x = map f x
  (Impure y f) <*> x = ?hole_2

Monad (Freer s t) where
  x >>= f = bind f x

||| Generalized algebraic data type to encode a request
data Request : Type -> Type where
  FileExists : String -> Request Bool
  ReadText : String -> Request String
  GetCwd : Request String

Response : {a : Type} -> Request a -> Type

silly : Freer (Request String) (Response)
silly = do
  cwd <- call GetCwd
  let path = cwd ++ "/hello-world.txt"
  exists <- call $ FileExists path
  if exists
  then call $ ReadText path
  else pure "Hello, World!"

service : Request a -> IO a
-- TODO how to implement this properly in Idris?
service (FileExists _) = pure True
service (ReadText path) = do
  -- `idris_crash` here is obviously lousy, but this is just a simple example
  -- program
  Right x <- readFile path | Left e => idris_crash (show e)
  pure x
service GetCwd = currentDir

main : IO ()
main = do
  msg <- unfree service silly
  putStrLn msg
