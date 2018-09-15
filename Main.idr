
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
    pure $ show (pretty la) ++ "\n\n"
        ++ show (pretty t)  ++ "\n"
        ++ if r then "true\n" else "false\n"
