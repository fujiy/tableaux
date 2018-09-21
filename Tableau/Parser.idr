
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

FormParser : Nat -> Type -> Type
FormParser n a = Vect n Name -> Parser (Vect n Name -> a)

runFP : FormParser 0 a -> Parser a
runFP p = flip id Nil <$> p Nil

lift1 : (a -> b) -> (c -> a) -> (c -> b)
lift1 = (.)

lift2 : (a -> b -> c) -> (d -> a) -> (d -> b) -> (d -> c)
lift2 f g h d = f (g d) (h d)

sign : List String -> Parser ()
sign = foldr (\s, p => skip (token s) <|>| p) (fail "empty list")

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

term ns = [| (lift2 Fun) (const <$> var) (terms ns) |]
     <|>| [| (variable ns) var |]

terms  ns = (\xs, ns' => map (flip id ns') xs)
       <$> (token "(" *>| (commaSep $ term ns) <* token ")")
terms' ns = terms ns <|> pure (const [])

quant : (Name -> (Name -> Form) -> Form) -> FormParser n Form

fact : FormParser n Form
conj : FormParser n Form
disj : FormParser n Form
impl : FormParser n Form
form : FormParser n Form

quant cons ns = do
    x <- var
    f <- fact (x::ns)
    pure $ \vs => cons x $ \v => f (v::vs)

fact ns = (sign ["forall", "∀"] *> quant Forall ns)
     <|>| (sign ["exists", "∃"] *> quant Exists ns)
     <|>| parens (form ns)
     <|>| [| (lift2 Equal) (term ns <* token "=") (term ns) |]
     <|>| [| (lift1 Neg)  (sign ["~", "¬"] *> fact ns) |]
     <|>| [| (lift2 Atom) (const <$> atom) (terms' ns) |]
conj ns = chainl1 (fact ns) (const (lift2 Conj) <$> sign ["&", "∧"])
disj ns = chainl1 (conj ns) (const (lift2 Disj) <$> sign ["|", "∨"])
impl ns = chainr1 (disj ns) (const (lift2 Impl) <$> sign ["->", "→"])
form ns = chainr1 (impl ns) (const (lift2 Equi) <$> sign ["<->", "↔"])

arg : Parser Argument
arg = [| LA (commaSep $ runFP form) (token "/" *> runFP form) |]
  <|> [| (LA []) (runFP form) |]

export
parse : String -> Either String Argument
-- parse : String -> Either String Form
parse = parseGeneric Nothing 4 $ spaces *> arg
