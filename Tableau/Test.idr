
module Tableau.Test

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class

import Tableau.Formula
import Tableau.Parser
import Tableau.Prover


assert : String -> Bool -> IO Bool
assert input result = do
    putStrLn $ "> " ++ input ++ "\n"
    case parse input of
        Left _ => do
            putStrLn "parse error."
            pure False
        Right la => do
            putStrLn $ displayS (renderPretty 1.0 80 $ pretty la) "\n"
            let (t, r) = prove la
            putStrLn $ displayS (renderPretty 1.0 80 $ pretty t) ""
            putStrLn $ if r then "true\n\n" else "false\n"
            pure $ r == result
    -- map (snd . prove) (parse input) == Right result

vailedInputs : List String
vailedInputs = [ "A / A | B"
               , "A & B / A"
               , "A | B, ~A / B"
               , "A -> B, A / B"
               , "A | B, A -> C, B -> C / C"
               , "A, ~A / B"
               , "B -> ~A, ~B -> C / A -> C"
               , "A <-> B / A -> B"
               , "~F(a) | exists x F(x), exists x F(x) -> P / F(a) -> P"
               , "T(c,b) -> forall x T(x, b), ~T(a,b) / ~T(c, b)"
               , "forall x M(x) / ~exists x ~ M(x)"
               , "exists x M(x) / ~forall x ~M(x)"
               , "forall x (P(x) -> Q(x)), P(a) / Q(a)"
               , "forall x (F(x) -> G(x)), forall x F(x) / G(a)"
               , "forall x (F(x) -> G(x)), forall x (G(x) -> H(x)) / forall x (F(x) -> H(x))"
               ]

export
testVailed : IO ()
testVailed = do
    rs <- traverse (flip assert True) vailedInputs
    if and (map Delay rs)
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"
