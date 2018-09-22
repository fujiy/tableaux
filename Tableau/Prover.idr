
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


just : Form -> (List Name, Form)
just f = ([], f)

justs : List Form -> List (List Name, Form)
justs = map just

step : ProveState -> (List Name, Form) -> List (List Name, Form) -> Prover (Tableau, Bool)

priority : ProveState -> (List Name, Form) -> Int

ordP : ProveState -> (List Name, Form) -> (List Name, Form) -> Ordering
ordP ps a b = compare (priority ps b) (priority ps a)

next : ProveState -> List (List Name, Form) -> List (List Name, Form) -> Prover (Tableau, Bool)
next ps fs news with (mergeBy (ordP ps) fs $ sortBy (ordP ps) news)
    | []     = return (End True, True)
    | (f::l) = if priority ps f >= 0 then step ps f l
                                     else next ps l []

names' : ProveState -> List Name
names' ps = if isNil (names ps) then ["a"] else names ps


DEFORM  : Int
ATOM    : Int
EXINST  : Int
UNIINST : Int
CONJ    : Int
DISJ    : Int
NONEQ   : Int
NONE    : Int
DEFORM  = 15
ATOM    = 10
EXINST  = 9
CONJ    = 7
UNIINST = 5
DISJ    = 3
NONEQ   = 2
NONE    = -1

-- priority _ = 0
priority ps (qns, f) = case f of
    Atom x xs          => ATOM
    Neg (Atom x xs)    => ATOM
    Neg (Neg a)        => DEFORM
    Conj a b           => CONJ
    Neg (Conj a b)     => DISJ
    Disj a b           => DISJ
    Neg (Disj a b)     => CONJ
    Impl a b           => DISJ
    Neg (Impl a b)     => CONJ
    Equi a b           => DISJ
    Neg (Equi a b)     => DISJ
    Forall _ gen       => if isNil (names' ps \\ qns) then NONE else UNIINST
    Neg (Forall x gen) => DEFORM
    Exists _ gen       => EXINST
    Neg (Exists x gen) => DEFORM
    Equal a b          => ATOM
    Neg (Equal a b)    => NONEQ

step ps (qns, f) l = call $ case f of
    Atom x xs =>
        if elemBy (\(x, xs), (y, ys) => x == y
                                     && equals (equalities ps) xs ys)
                  (x, xs) (falseAtoms ps)
        then return (End False, False)
        else next (record { trueAtoms = (x, xs) :: trueAtoms ps } ps) l []

    Neg (Atom x xs) =>
        if elemBy (\(x, xs), (y, ys) => x == y
                                     && equals (equalities ps) xs ys)
                  (x, xs) (trueAtoms ps)
        then return (End False, False)
        else next (record { falseAtoms = (x, xs) :: falseAtoms ps } ps) l []

    Neg (Neg a) =>
        mapP (next ps l $ justs [a])
        $ \(t, r) => (Follow a t, r)

    Conj a b =>
        mapP (next ps l $ justs [a, b])
        $ \(t, r) => (Follow a (Follow b t), r)

    Neg (Conj a b) =>
        app (next ps l $ justs [Neg a])
            (next ps l $ justs [Neg b])
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow (Neg a) ta)
                    (Follow (Neg b) tb),
             ra || rb)

    Disj a b =>
        app (next ps l $ justs [a])
            (next ps l $ justs [b])
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow a ta)
                    (Follow b tb),
             ra || rb)

    Neg (Disj a b) =>
        mapP (next ps l $ justs [Neg a, Neg b])
        $ \(t, r) => (Follow (Neg a) (Follow (Neg b) t), r)

    Impl a b =>
        app (next ps l $ justs [Neg a])
            (next ps l $ justs [b])
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow (Neg a) ta)
                    (Follow b tb),
             ra || rb)

    Neg (Impl a b) =>
        mapP (next ps l $ justs [a, Neg b])
        $ \(t, r) => (Follow a (Follow (Neg b) t), r)

    Equi a b =>
        app (next ps l $ justs [a, b])
            (next ps l $ justs [Neg a, Neg b])
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow a       (Follow b       ta))
                    (Follow (Neg a) (Follow (Neg b) tb)),
             ra || rb)

    Neg (Equi a b) =>
        app (next ps l $ justs [a, Neg b])
            (next ps l $ justs [Neg a, b])
        $ \(ta, ra), (tb, rb) =>
            (Branch (Follow a       (Follow (Neg b) ta))
                    (Follow (Neg a) (Follow b       tb)),
             ra || rb)

    Forall _ gen =>
        -- case names' ps \\ qns of
        --     [] => next ps l []
        --     n::ns =>
        --         let i = gen n
        --         in  mapP (next (record { names = names' ps } ps) l
        --                 $ (n::qns, f) :: justs [i])
        --             $ \(t, r) => (Follow i t, r)
        let ns' = names' ps \\ qns
            is  = gen <$> ns'
        in  mapP (next (record { names = names' ps } ps) l
                $ (ns' ++ qns, f) :: justs is)
            $ \(t, r) => (foldr Follow t is, r)

    Neg (Forall x gen) =>
        mapP (next ps l $ justs [Exists x (Neg . gen)])
        $ \(t, r) => (Follow (Exists x (Neg . gen)) t, r)

    Exists _ gen =>
        let n = new $ names ps
        in  mapP (next (record { names = n::names ps } ps) l $ justs [gen n])
            $ \(t, r) => (Follow (gen n) t, r)

    Neg (Exists x gen) =>
        mapP (next ps l $ justs [Forall x (Neg . gen)])
        $ \(t, r) => (Follow (Forall x (Neg . gen)) t, r)

    Equal a b =>
        next (record { equalities = (a, b)::equalities ps } ps) l []

    Neg (Equal a b) =>
        if equal (equalities ps) a b
        then return (End False, False)
        else next ps l []

export
prove : Argument -> (Tableau, Bool)
prove (LA ps c) =
    let ini    = ps ++ [Neg c]
        (t, r) = runProver (next (MkPS (vars ini) [] [] []) [] $ justs ini) 127 (Limit, True)
    in  (foldr Follow t ini, not r)
