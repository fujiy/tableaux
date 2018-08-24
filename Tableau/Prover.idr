
module Tableau.Prover

import Tableau.Formula

step : List Name -> List Name -> List Form -> (Tableau, Bool)
step ts fs [] = (End True, True)
step ts fs (f::l) = case f of
    Atom x =>
        if elem x fs
        then (End False, False)
        else step (x::ts) fs l
    Neg (Atom x) =>
        if elem x ts
        then (End False, False)
        else step ts (x::fs) l
    Neg (Neg a) =>
        let (t, r) = step ts fs (a::l)
        in  (Follow a t, r)
    Conj a b =>
        let (t, r) = step ts fs (a::b::l)
        in  (Follow a (Follow b t), r)
    Neg (Conj a b) =>
        let (ta, ra) = step ts fs (Neg a::l)
            (tb, rb) = step ts fs (Neg b::l)
        in  (Branch (Follow (Neg a) ta)
                    (Follow (Neg b) tb),
             ra || rb)
    Disj a b =>
        let (ta, ra) = step ts fs (a::l)
            (tb, rb) = step ts fs (b::l)
        in  (Branch (Follow a ta)
                    (Follow b tb),
             ra || rb)
    Neg (Disj a b) =>
        let (t, r) = step ts fs (Neg a::Neg b::l)
        in  (Follow (Neg a) (Follow (Neg b) t), r)
    Impl a b =>
        let (ta, ra) = step ts fs (Neg a::l)
            (tb, rb) = step ts fs (b::l)
        in  (Branch (Follow (Neg a) ta)
                    (Follow b tb),
             ra || rb)
    Neg (Impl a b) =>
        let (t, r) = step ts fs (a::Neg b::l)
        in  (Follow a (Follow (Neg b) t), r)
    Equi a b =>
        let (tx, rx) = step ts fs (a::b::l)
            (ty, ry) = step ts fs (Neg a::Neg b::l)
        in  (Branch (Follow a       (Follow b       tx))
                    (Follow (Neg a) (Follow (Neg b) ty)),
             rx || ry)
    Neg (Equi a b) =>
        let (tx, rx) = step ts fs (a::Neg b::l)
            (ty, ry) = step ts fs (Neg a::b::l)
        in  (Branch (Follow a       (Follow (Neg b) tx))
                    (Follow (Neg a) (Follow b       ty)),
             rx || ry)

export
prove : Argument -> (Tableau, Bool)
prove (LA ps c) = let ini = ps ++ [Neg c]
                      (t, r) = step [] [] ini
                  in  (foldr Follow t ini, not r)
