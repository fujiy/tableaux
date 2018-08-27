
module Tableau.Prover


import Tableau.Formula

new : List Name -> Name
new = try 'a'
    where
        try : Char -> List Name -> Name
        try c ns =
            if elem (singleton c) ns
            then try (succ c) ns
            else singleton c

inst : List Name -> List (Name, List Term) -> List (Name, List Term) -> List (Name -> Form) -> (Tableau, Bool)
step : List Name -> List (Name, List Term) -> List (Name, List Term) -> List (Name -> Form) -> List Form -> (Tableau, Bool)

inst ns ts fs []  = (End True, True)
inst ns ts fs uqs = let is     = uqs <*> ns
                        (t, r) = step ns ts fs [] is
                    in  (foldr Follow t is, r)

step ns ts fs uqs [] = inst ns ts fs uqs
step ns ts fs uqs (f::l) = case f of
    Atom x xs =>
        if elem (x, xs) fs
        then (End False, False)
        else step ns ((x, xs)::ts) fs uqs l
    Neg (Atom x xs) =>
        if elem (x, xs) ts
        then (End False, False)
        else step ns ts ((x, xs)::fs) uqs l
    Neg (Neg a) =>
        let (t, r) = step ns ts fs uqs (a::l)
        in  (Follow a t, r)
    Conj a b =>
        let (t, r) = step ns ts fs uqs (a::b::l)
        in  (Follow a (Follow b t), r)
    Neg (Conj a b) =>
        let (ta, ra) = step ns ts fs uqs (Neg a::l)
            (tb, rb) = step ns ts fs uqs (Neg b::l)
        in  (Branch (Follow (Neg a) ta)
                    (Follow (Neg b) tb),
             ra || rb)
    Disj a b =>
        let (ta, ra) = step ns ts fs uqs (a::l)
            (tb, rb) = step ns ts fs uqs (b::l)
        in  (Branch (Follow a ta)
                    (Follow b tb),
             ra || rb)
    Neg (Disj a b) =>
        let (t, r) = step ns ts fs uqs (Neg a::Neg b::l)
        in  (Follow (Neg a) (Follow (Neg b) t), r)
    Impl a b =>
        let (ta, ra) = step ns ts fs uqs (Neg a::l)
            (tb, rb) = step ns ts fs uqs (b::l)
        in  (Branch (Follow (Neg a) ta)
                    (Follow b tb),
             ra || rb)
    Neg (Impl a b) =>
        let (t, r) = step ns ts fs uqs (a::Neg b::l)
        in  (Follow a (Follow (Neg b) t), r)
    Equi a b =>
        let (tx, rx) = step ns ts fs uqs (a::b::l)
            (ty, ry) = step ns ts fs uqs (Neg a::Neg b::l)
        in  (Branch (Follow a       (Follow b       tx))
                    (Follow (Neg a) (Follow (Neg b) ty)),
             rx || ry)
    Neg (Equi a b) =>
        let (tx, rx) = step ns ts fs uqs (a::Neg b::l)
            (ty, ry) = step ns ts fs uqs (Neg a::b::l)
        in  (Branch (Follow a       (Follow (Neg b) tx))
                    (Follow (Neg a) (Follow b       ty)),
             rx || ry)
    Forall _ gen =>
        step ns ts fs (gen::uqs) l
    Neg (Forall x gen) =>
        let n      = new ns
            (t, r) = step (n::ns) ts fs uqs (Neg (gen n)::l)
        in  (Follow (Neg (gen n)) t, r)
    Exists _ gen =>
        let n      = new ns
            (t, r) = step (n::ns) ts fs uqs (gen n::l)
        in  (Follow (gen n) t, r)
    Neg (Exists _ gen) =>
        step ns ts fs (Neg . gen ::uqs) l

export
prove : Argument -> (Tableau, Bool)
prove (LA ps c) = let ini    = ps ++ [Neg c]
                      (t, r) = step (vars ini) [] [] [] ini
                  in  (foldr Follow t ini, not r)
