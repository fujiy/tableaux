
module Tableau.Parser

import Lightyear
import Lightyear.Char
import Lightyear.Strings
import Lightyear.Combinators

import Tableau.Formula

atom : Parser Form
atom = Atom . pack <$> lexeme (some upper)

term : Parser Form
conj : Parser Form
disj : Parser Form
impl : Parser Form
form : Parser Form

term = atom
  <|>| (Neg <$> (token "~" *> term))
  <|>| parens form
conj = chainl1 term (const Conj <$> token "&")
disj = chainl1 conj (const Disj <$> token "|")
impl = chainr1 disj (const Impl <$> token "->")
form = chainr1 impl (const Equi <$> token "<->")

export
parse : String -> Either String Form
parse = parseGeneric Nothing 4 $ spaces *> form
