
module Tableau.Formula

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class

public export
Name : Type
Name = String

public export
data Form = Atom Name
          | Neg Form
          | Conj Form Form
          | Disj Form Form
          | Impl Form Form
          | Equi Form Form

pform : Form -> Doc

export
Pretty Form where
    pretty (Atom x)   = text x
    pretty (Neg a)    = text "¬" |+| pform a
    pretty (Conj a b) = pform a |++| text "∧" |++| pform b
    pretty (Disj a b) = pform a |++| text "∨" |++| pform b
    pretty (Impl a b) = pform a |++| text "→" |++| pform b
    pretty (Equi a b) = pform a |++| text "↔" |++| pform b

pform (Atom x) = pretty $ Atom x
pform (Neg a)  = pretty $ Neg a
pform a        = parens $ pretty a

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
