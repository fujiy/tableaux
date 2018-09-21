
module Tableau.Prover


import Tableau.Formula

record Prover (a : Type) where
    constructor P
    runProver : Nat -> a -> a

return : a -> Prover a
return a = P $ \_, _ => a

call : Prover a -> Prover a
call p = P $ \lim, default =>
    if lim == 0 then default
                else runProver p (minus lim 1) default

mapP : Prover a -> (a -> a) -> Prover a
mapP p f = P $ \lim, default =>
    f $ runProver p lim default

app : Prover a -> Prover a -> (a -> a -> a) -> Prover a
app pa pb f = P $ \lim, default =>
    f (runProver pa lim default) (runProver pb lim default)

record ProveState where
    constructor MkPS
    names      : List Name
    equalities : List (Term, Term)
    trueAtoms  : List (Name, List Term)
    falseAtoms : List (Name, List Term)
    univQuants : List (Name -> Form)

new : List Name -> Name
new = try 'a'
    where
        try : Char -> List Name -> Name
        try c ns =
            if elem (singleton c) ns
            then try (succ c) ns
            else singleton c

equal  : List (Term, Term) -> Term -> Term -> Bool
equals : List (Term, Term) -> List Term -> List Term -> Bool

equal eqs a b
    = case (a, b) of
        (Var x,    Var y)    => x == y
        (Fun x xs, Fun y ys) => equal eqs (Var x) (Var y)
                             && equals eqs xs ys
        _ => False
   || go [] eqs a b
    where
        go : List (Term, Term) -> List (Term, Term) -> Term -> Term -> Bool
        go exs []            a b = False
        go exs ((x, y)::eys) a b
            = equal (exs ++ eys) x a && equal (exs ++ eys) y b
           || equal (exs ++ eys) x b && equal (exs ++ eys) y a
           || go (exs ++ [(x, y)]) eys a b

equals _   []      []      = True
equals _   []      _       = False
equals _   _       []      = False
equals eqs (a::as) (b::bs) = equal eqs a b && equals eqs as bs

inst : ProveState -> Prover (Tableau, Bool)
step : ProveState -> List Form -> Prover (Tableau, Bool)

inst ps with (univQuants ps)
    | [] = return (End True, True)
    | us = let ns' = if isNil (names ps) then ["a"] else names ps
               is   = us <*> ns'
           in  mapP (step (record { names = ns' } ps) is)
                $ \(t, r) => (foldr Follow t is, r)

step ps [] = inst ps
step ps (f::l) = call $ case f of
    Atom x xs =>
        if elemBy (\(x, xs), (y, ys) => x == y
                                     && equals (equalities ps) xs ys)
                  (x, xs) (falseAtoms ps)
        then return (End False, False)
        else step (record { trueAtoms = (x, xs) :: trueAtoms ps } ps) l

    Neg (Atom x xs) =>
        if elemBy (\(x, xs), (y, ys) => x == y
                                     && equals (equalities ps) xs ys)
                  (x, xs) (trueAtoms ps)
        then return (End False, False)
        else step (record { falseAtoms = (x, xs) :: falseAtoms ps } ps) l

    Neg (Neg a) =>
        mapP (step ps $ a::l)
        $ \(t, r) => (Follow a t, r)

    Conj a b =>
        mapP (step ps $ a::b::l)
        $ \(t, r) => (Follow a (Follow b t), r)

    Neg (Conj a b) =>
        app (step ps $ Neg a::l)
            (step ps $ Neg b::l)
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow (Neg a) ta)
                    (Follow (Neg b) tb),
             ra || rb)

    Disj a b =>
        app (step ps $ a::l)
            (step ps $ b::l)
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow a ta)
                    (Follow b tb),
             ra || rb)

    Neg (Disj a b) =>
        mapP (step ps $ Neg a::Neg b::l)
        $ \(t, r) => (Follow (Neg a) (Follow (Neg b) t), r)

    Impl a b =>
        app (step ps $ Neg a::l)
            (step ps $ b::l)
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow (Neg a) ta)
                    (Follow b tb),
             ra || rb)

    Neg (Impl a b) =>
        mapP (step ps $ a::Neg b::l)
        $ \(t, r) => (Follow a (Follow (Neg b) t), r)

    Equi a b =>
        app (step ps $ a::b::l)
            (step ps $ Neg a::Neg b::l)
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow a       (Follow b       ta))
                    (Follow (Neg a) (Follow (Neg b) tb)),
             ra || rb)

    Equi a b =>
        app (step ps $ a::Neg b::l)
            (step ps $ Neg a::b::l)
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow a       (Follow (Neg b) ta))
                    (Follow (Neg a) (Follow b       tb)),
             ra || rb)

    Forall _ gen =>
        step (record { univQuants = gen::univQuants ps} ps) l

    Neg (Forall x gen) =>
        step ps $ Exists x (Neg . gen)::l

    Exists _ gen =>
        let n = new $ names ps
        in  mapP (step (record { names = n::names ps } ps) $ gen n::l)
            $ \(t, r) => (Follow (gen n) t, r)

    Neg (Exists x gen) =>
        step ps $ Forall x (Neg . gen)::l

    Equal a b =>
        step (record { equalities = (a, b)::equalities ps } ps) l

    Neg (Equal a b) =>
        if equal (equalities ps) a b
        then return (End False, False)
        else step ps l

export
prove : Argument -> (Tableau, Bool)
prove (LA ps c) =
    let ini    = ps ++ [Neg c]
        (t, r) = runProver (step (MkPS (vars ini) [] [] [] []) ini) 50 (End True, True)
    in  (foldr Follow t ini, not r)
