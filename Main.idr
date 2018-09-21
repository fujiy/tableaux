
module Main

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class

import Tableau.Formula
import Tableau.Parser
import Tableau.Prover

alter : Either a b -> Either a b -> Either a b
alter x y = either (const y) Right x

main : IO ()
main = repl "> " $ \s => fromEither	$ do
    la <- alter (parse s) (Left "parse error.\n")
    let (t, r) = prove la
    pure $ displayS (renderPretty 1.0 80 $ pretty la) "\n\n"
        ++ displayS (renderPretty 1.0 1000 $ pretty t) "\n"
        ++ if r then "true\n" else "false\n"
