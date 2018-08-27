
module Tableau.Parser

import Data.Fin
import Data.Vect

import Lightyear
import Lightyear.Char
import Lightyear.Strings
import Lightyear.Combinators

import Tableau.Formula


elemIndex' : Eq elem => (x : elem) -> (xs : Vect n elem) -> (p : Elem x xs) -> Fin n
elemIndex' x _ Here = FZ
elemIndex' x (_ :: xs) (There later) = FS $ elemIndex' x xs later

-- quant : (Name -> (Name -> Form) -> Form) -> Name -> Form -> Form
-- quant cons f =
--     where
--         go : Vec n Name -> Form -> (Vec n Name -> Form)
--         go (Atom x') with (x == x')
--             | True = \y -> Atom y
--             | _    = const (Atom x')
--         go (Forall x' f) with (x == x')
--             | True = const (Forall x' f)
--             | _    = [| (Forall x') (go $ f x') |]
--         -- go (Exists x' f) with (x == x')
--         --     | True = const (Exists x' f)
--         --     | _    = [| (Exists x') (go $ f x') |]
--         go (Neg a)    = [| Neg (go a) |]
--         go (Conj a b) = [| Conj (go a) (go b) |]
--         go (Disj a b) = [| Disj (go a) (go b) |]
--         go (Impl a b) = [| Impl (go a) (go b) |]
--         go (Equi a b) = [| Equi (go a) (go b) |]

data VFun : Nat -> Type -> Type -> Type where
    FunZ : b -> VFun 0 a b
    FunS : (a -> VFun n a b) -> VFun (S n) a b

ret : b -> VFun 0 a b
ret = FunZ

app : VFun (S n) a b -> a -> VFun n a b
app (FunS f) a = f a

-- quant : Vect n Name -> Form -> (Vect n Name -> Form)
-- quant ns f = case f of
--     Forall x gen => \vs => Forall x (\v => quant (x::ns) (gen "") (v::vs))
--     _ => \_ => f


    -- case f of
    --     Forall x gen => \vs => Forall x (\v => quant (x::ns) (gen "") (v::vs))
    -- _ => \_ => f

FormParser : Nat -> Type -> Type
FormParser n a = Vect n Name -> Parser (Vect n Name -> a)

runFP : FormParser 0 a -> Parser a
runFP p = flip id Nil <$> p Nil

-- atom : Parser Form
-- atom = Atom <$> name

lift1 : (a -> b) -> (c -> a) -> (c -> b)
lift1 = (.)

lift2 : (a -> b -> c) -> (d -> a) -> (d -> b) -> (d -> c)
lift2 f g h d = f (g d) (h d)


var : Parser Name
var = pack <$> lexeme (some lower)

atom : Parser Name
atom = pack <$> lexeme (some upper)

variable : Vect n Name -> Name -> (Vect n Name -> Term)
variable ns x = case isElem x ns of
    Yes p => Var . index (elemIndex' x ns p)
    No _  => const $ Var x

term   : FormParser n Term
terms  : FormParser n (List Term)
terms' : FormParser n (List Term)

term ns = [| (variable ns) var |]
     <|>| [| (lift2 Fun) (const <$> var) (terms ns) |]

terms  ns = (\xs, ns' => map (flip id ns') xs) <$> parens (commaSep $ term ns)
terms' ns = terms ns <|> pure (const [])


-- Vect n Name -> m (Name -> a)
-- Vect n Name -> m Name -> m a
-- (Vect n Name, Name) -> m a

-- Name -> m a
-- m (Name -> m a)
-- m (Name -> a)

-- foo : Monad m => (Name -> Parser a) -> Parser (Name -> a)
-- foo f = PT $ \r, us, cs, ue, ce
--         =>

-- Name -> (Name -> a)

-- quant : (Name -> (Name -> Form) -> Form) -> FormParser n Form
-- quant cons ns = do
--     token "forall"
--     x <- name
--     dot
--     case isElem x ns of
--         Yes p => fact ns
--         No _ => do
--             _ <- (fact (x::ns) <*> )
--
--             Forall x (x ->

quant : (Name -> (Name -> Form) -> Form) -> FormParser n Form

fact : FormParser n Form
conj : FormParser n Form
disj : FormParser n Form
impl : FormParser n Form
form : FormParser n Form

quant cons ns = do
    x <- var
    dot
    f <- form (x::ns)
    pure $ \vs => cons x $ \v => f (v::vs)

fact ns = (token "forall" *> quant Forall ns)
     <|>| (token "exists" *> quant Exists ns)
     <|>| parens (form ns)
     <|>| [| (lift1 Neg) (token "~" *> fact ns) |]
     <|>| [| (lift2 Atom) (const <$> atom) (terms' ns) |]
conj ns = chainl1 (fact ns) (const (lift2 Conj) <$> token "&")
disj ns = chainl1 (conj ns) (const (lift2 Disj) <$> token "|")
impl ns = chainr1 (disj ns) (const (lift2 Impl) <$> token "->")
form ns = chainr1 (impl ns) (const (lift2 Equi) <$> token "<->")

arg : Parser Argument
arg = [| LA (commaSep $ runFP form) (token "/" *> runFP form) |]

export
-- parse : String -> Either String Argument
parse : String -> Either String Form
parse = parseGeneric Nothing 4 $ spaces *> runFP form
