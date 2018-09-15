
module Text.PrettyPrint.Boxes

import Text.PrettyPrint.Leijen
import Text.PrettyPrint.Leijen.Class


public export
data Alignment = Center
               | First
               | Last

Content : Type

export
record Box where
    constructor MkBox
    height, width : Int
    alignment : Alignment
    content : Content


data Content = Blank
             | Text String
             | Row (List Box)
             | Column (List Box)

infixr 5 ||$|, ||$$|
infixr 6 ||+|, ||++|

-- export
-- box :: List Row -> Box
-- box = Box

export
textb : String -> Box
textb s = MkBox 1 (toIntNat $ length s) First $ Text s

export
blank : Int -> Int -> Box
blank h w = MkBox h w First Blank

export
vcatb : List Box -> Box
vcatb bs = let h = sum $ map height bs
               w = foldr (max . width) 0 bs
           in  MkBox h w First $ Column bs

export
hcatb : List Box -> Box
hcatb bs = let h = foldr (max . height) 0 bs
               w = sum $ map width bs
           in  MkBox h w First $ Row bs

export
docb : Doc -> Box
docb = vcatb . map textb . lines . show

export
alignb : Alignment -> Box -> Box
alignb a (MkBox h w _ c) = MkBox h w a c

export
(||+|) : Box -> Box -> Box
l ||+| r = hcatb [l, r]

export
(||++|) : Box -> Box -> Box
l ||++| r = hcatb [l, blank 0 1, r]

export
(||$|) : Box -> Box -> Box
l ||$| r = vcatb [l, r]

export
(||$$|) : Box -> Box -> Box
l ||$$| r = vcatb [l, blank 1 0, r]

-- prettyb : Box -> Doc
-- prettyb (Box h w c) = case c of

zipWithDefault : (f : a -> b -> c) -> (ld : a) -> (rd : b) -> (l : List a) -> (r : List b) -> List c
zipWithDefault f ld rd []      []      = []
zipWithDefault f ld rd []      (y::ys) = f ld y :: zipWithDefault f ld rd [] ys
zipWithDefault f ld rd (x::xs) []      = f x rd :: zipWithDefault f ld rd xs []
zipWithDefault f ld rd (x::xs) (y::ys) = f x y  :: zipWithDefault f ld rd xs ys

replicate' : (i : Int) -> (x : a) -> List a
replicate' i x with (i <= 0)
    | True  = []
    | False = x :: replicate' (i - 1) x

total
toDocs : Box -> List Doc
toDocs (MkBox h w a c) = assert_total $ case c of
    Blank     => []
    Text s    => [text s]
    Row bs    => foldr (zipWith (|+|)) (replicate' h empty)
               $ map (\b => fillColumn h (width b) $ toDocs b) bs
    Column bs => concatMap (\b => alignDocs a w (width b) $ toDocs b) bs

  where
    -- toDoc' : Int -> Int -> Alignment -> Content -> Doc
    -- toDoc' h w a c = fillDocs h w $ case c of
    --     Blank     => []
    --     Text s    => [text s]
    --     Row bs    => foldr (zipWithDefault (|+|) (fill w empty))
    --                $ map (\(Box h' w' a' c') fillColumn h . toDoc) bs
    --     Column bs => concatMap toDoc bs

    alignDocs : Alignment -> Int -> Int -> List Doc -> List Doc
    alignDocs a w' w = map $ case a of
        Center => fill w' . indent (div (w' - w - 1) 2)
        First  => fill w'
        Last   => indent (w' - w)

    fillColumn : Int -> Int -> List Doc -> List Doc
    fillColumn h w ds = ds ++ replicate' (h - toIntNat (length ds)) (fill w empty)

    fillDocs : Int -> Int -> List Doc -> List Doc
    fillDocs h w ds = fillColumn h w $ map (fill w) ds

export
Pretty Box where
    pretty = vsep . toDocs
