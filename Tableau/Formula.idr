
module Tableau.Formula

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class

public export
data Form = Atom String
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


data 


-- unfoldr : (b -> Maybe (a, b)) -> b -> List a
-- unfoldr f b = maybe [] (\(a, b') => a :: unfoldr f b') (f b)
--
-- unfoldl : (b -> Maybe (b, a)) -> b -> List a
-- unfoldl f b = maybe [] (\(b', a) => unfoldl f b' ++ [a]) (f b)
