
module Tableau.Test

import Tableau.Formula
import Tableau.Parser
import Tableau.Prover


assert : String -> Bool -> Bool
assert input result = map (snd . prove) (parse input) == Right result

export
testVailed : IO ()
testVailed = if all (flip assert True)
    [ "A / A | B"
    , "A & B / A"
    , "A | B, ~A / B"
    , "A -> B, A / B"
    , "A | B, A -> C, B -> C / C"
    , "A, ~A / B"
    , "B -> ~A, ~B -> C / A -> C"
    , "A <-> B / A -> B"
    ]
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"
