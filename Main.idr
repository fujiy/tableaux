
module Main

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class

import Tableau.Formula
import Tableau.Parser

alter : Either a b -> Either a b -> Either a b
alter x y = either (const y) Right x

main : IO ()
main = repl "> " $ \s => fromEither	$ do
    a <- alter (parse s) (Left "parse error.\n")
    pure $ displayS (renderCompact $ pretty a) "\n"
