
module Tableau.Formula

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class

%default total

public export
Name : Type
Name = String

public export
data Term = Var Name
          | Fun Name (List Term)

public export
data Form = Atom Name (List Term)
          | Neg Form
          | Conj Form Form
          | Disj Form Form
          | Impl Form Form
          | Equi Form Form
          | Forall Name (Name -> Form)
          | Exists Name (Name -> Form)

pform : Form -> Doc

ptl : List Term -> List Doc

public export
Pretty Term where
    pretty (Var x)    = text x
    pretty (Fun x ts) = text x |+| tupled (ptl ts)

ptl [] = []
ptl (x::xs) = pretty x :: ptl xs

export
Pretty Form where
    pretty (Atom x [])  = text x
    pretty (Atom x ts)  = text x |+| tupled (map pretty ts)
    pretty (Neg a)      = text "¬" |+| pform a
    pretty (Conj a b)   = pform a |++| text "∧" |++| pform b
    pretty (Disj a b)   = pform a |++| text "∨" |++| pform b
    pretty (Impl a b)   = pform a |++| text "→" |++| pform b
    pretty (Equi a b)   = pform a |++| text "↔" |++| pform b
    pretty (Forall x f) = text "∀" |+| text x |+| dot |+| pform (f $ "\'"++x)
    pretty (Exists x f) = text "∃" |+| text x |+| dot |+| pform (f $ "\'"++x)

pform (Atom x ts)  = pretty $ Atom x ts
pform (Neg a)      = pretty $ Neg a
pform (Forall x f) = pretty $ Forall x f
pform (Exists x f) = pretty $ Forall x f
pform a            = parens $ pretty a

public export
data Argument = LA (List Form) Form

export
Pretty Argument where
    pretty (LA ps c) = vsep (map pretty ps)
                   |+| text "--------"
                   |$| pretty c

public export
data Tableau = Follow Form Tableau
             | Branch Tableau Tableau
             | End Bool

export
Pretty Tableau where
    pretty (Follow f t) = pretty f |$| pretty t
    pretty (Branch x y) = indent 2 (pretty x |$| pretty y)
    pretty (End True)   = empty
    pretty (End False)  = text "×" |$| empty
