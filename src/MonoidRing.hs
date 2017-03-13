{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, GeneralizedNewtypeDeriving, RoleAnnotations #-}

module MonoidRing where

import Data.List
import Data.Monoid
import Data.Coerce
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language (haskellDef)
import qualified Text.ParserCombinators.Parsec.Token as P

import Debug.Trace
import Test.QuickCheck

import Srs

class (Monoid a) => Group a where
  ginv :: a -> a

class (Num k, Group m) => Mod k m where
  modscal :: k -> m -> m

newtype FreeMod k s = FreeMod [(k, s)] deriving (Eq, Arbitrary)

monomFM :: k -> s -> FreeMod k s
monomFM n w = FreeMod [(n, w)]

simplify :: (Num k, Eq k, Eq s) => FreeMod k s -> FreeMod k s
simplify (FreeMod []) = FreeMod []
simplify (FreeMod (x:xs)) = coerce f $ simplify $ FreeMod xs2
  where
    (xs1, xs2) = partition (\(_, w) -> w == snd x) (x:xs)
    s = sum $ map fst xs1
    f = if s == fromInteger 0 then id else ((s, snd x) :)

plusFM' :: (Num k, Eq k, Eq a) => FreeMod k a -> (k, a) -> FreeMod k a
plusFM' (FreeMod x) (n, w) = coerce f x2
  where
    (x1, x2) = partition (\(_, w') -> w == w') ((n, w):x)
    s = sum $ map fst x1
    f = if s == fromInteger 0 then id else ((s, w) :)

plusFM :: (Num k, Eq k, Eq a) => FreeMod k a -> FreeMod k a -> FreeMod k a
plusFM x (FreeMod y) = foldl plusFM' x y

fm0 = FreeMod []

instance (Num k, Eq k, Eq a) => Monoid (FreeMod k a) where
  mempty = FreeMod []
  mappend = plusFM

instance (Num k, Eq k, Eq a) => Group (FreeMod k a) where
  ginv (FreeMod x) = FreeMod $ map (\(n, a) -> (-n, a)) x

gdiv :: (Group g) => g -> g -> g
gdiv a b = a `mappend` ginv b

instance (Num k, Eq k, Eq a) => Mod k (FreeMod k a) where
  modscal n (FreeMod x) = FreeMod $ map (\(m, a) -> (m * n, a)) x
 
multFM' :: (Num k, Eq k, Monoid a, Eq a) => FreeMod k a -> (k, a) -> FreeMod k a
multFM' (FreeMod mr) (n, w)
  | n == fromInteger 0 = fm0
  | otherwise = foldl f fm0 mr
  where
    f mr' (n', w') = plusFM' mr' (n * n', mappend w w')

multFM :: (Num k, Eq k, Monoid a, Eq a) => FreeMod k a -> FreeMod k a -> FreeMod k a
multFM (FreeMod mr1) mr2 = foldl f fm0 mr1
  where f mr (w, n) = mappend (multFM' mr2 (w, n)) mr
 
instance (Num k, Eq k, Monoid a, Eq a) => Num (FreeMod k a) where
  (+) = plusFM
  (-) = gdiv
  (*) = multFM
  abs = id
  signum _ = FreeMod [(fromInteger 1, mempty)]
  fromInteger n = if n == 0 then fm0 else FreeMod [(fromInteger n, mempty)]

type MR = FreeMod Integer String

instance (Show k, Eq k, Num k, Show a) => Show (FreeMod k a) where
  show (FreeMod x) = intercalate " + " $ map (\(n, s) -> show s ++  "." ++ "(" ++ show n ++ ")") x


redMR :: SRS -> MR -> MR
redMR rules (FreeMod mr) = foldl f (FreeMod []) mr
  where
    f mr' (n, w) = FreeMod [(n,normalForm rules w)] + mr'

liftFM :: (Num k, Eq k, Eq a, Group g, Mod k g) => (a -> g) -> FreeMod k a -> g
liftFM f (FreeMod x) = foldl (\x' (n, w) -> mappend x' (modscal n (f w))) mempty x

lookup' :: (Eq a, Show a) => a -> [(a, b)] -> b
lookup' a [] = error $ "no elem: " ++ show a
lookup' a ((a', b):rest) = if a == a' then b else lookup' a rest

liftFMTable :: (Num k, Eq k, Eq a, Show a, Group g, Mod k g) => [(a, g)] -> FreeMod k a -> g
liftFMTable table (FreeMod x) = foldl (\x' (n, w) -> mappend x' (modscal n $ lookup' w table)) mempty x


-- Kobayashi's resolution

intersc :: String -> String -> [String]
intersc w1 w2 = map (flip splitAt w2) [1..length w2 - 1] >>= (\(x, y) -> if isSuffixOf x w1 then [y] else [])

gen :: Int -> [Char] -> SRS -> [[String]]
gen 1 alpha _ = map (\a -> [[a]]) alpha
gen n alpha rules = [ g ++ [w] | g <- gen (n-1) alpha rules, w <- map fst rules >>= intersc (last g), isRMinimal rules (last g ++ w) ]

trans :: FreeMod MR [String] -> FreeMod Integer [String]
trans (FreeMod []) = FreeMod []
trans (FreeMod ((FreeMod a, g):x)) = FreeMod ((map (\(n,w) -> (n, g ++ [w])) a) ++ y)
  where
    FreeMod y = trans (FreeMod x)

transInv :: FreeMod Integer [String] -> FreeMod MR [String]
transInv (FreeMod []) = FreeMod []
transInv (FreeMod ((n,[a]):x)) = simplify $ FreeMod ((monomFM n "", [a]) : coerce transInv x)
transInv (FreeMod ((n,g):x)) = simplify $ FreeMod ((monomFM n (last g), init g) : coerce transInv x)

del1 :: [Char] -> FreeMod MR [String] -> FreeMod MR [String]
del1 alpha x = liftFMTable (map (\x -> ([[x]], monomFM (FreeMod [(1, [x]), (-1, "")]) [])) alpha) x

inn1 :: SRS -> FreeMod MR [String] -> FreeMod MR [String]
inn1 rules (FreeMod [(x, [])]) = transInv $ liftFM inn1' $ redMR rules x
  where
    inn1' :: String -> FreeMod Integer [String]
    inn1' [] = FreeMod []
    inn1' [a] = monomFM 1 [[a]]
    inn1' (a:r) = monomFM 1 [[a], r] `mappend` inn1' r

del :: Int -> [Char] -> SRS -> FreeMod MR [String] -> FreeMod MR [String]
del 1 alpha _ x = del1 alpha x
del n alpha rules x = liftFMTable table x
  where
    table :: [([String], FreeMod MR [String])]
    table = map (\g -> let g' = monomFM (monomFM 1 $ last g) $ init g in
                       (g, g' `gdiv` inn (n-1) alpha rules (del (n-1) alpha rules g')))
                $ gen n alpha rules

decomp :: SRS -> String -> String -> (String, String)
decomp rules v w = head $ filter (\(w1, w2) -> isRMinimal rules (v ++ w1)) $ map (flip splitAt w) [length w, length w - 1..1]

inn :: Int -> [Char] -> SRS -> FreeMod MR [String] -> FreeMod MR [String]
inn 1 _ rules x = inn1 rules x
inn n alpha rules x = transInv $ liftFM inn' $ trans x
  where
    inn' :: [String] -> FreeMod Integer [String]
    inn' x' = let w = normalForm rules $ last x' in
              let w' = last $ init x' in
              if isIrr rules $ w' ++ w
                then FreeMod []
                else let (x1, x2) = decomp rules w' w in
                     monomFM 1 (init x' ++ [x1, x2]) `mappend`
                       trans (inn n alpha rules $ modscal (monomFM 1 x2 :: MR) $ inn (n-1) alpha rules $ del (n-1) alpha rules $ monomFM (monomFM 1 x1) (init x'))


-- parser

lexer = P.makeTokenParser (haskellDef { P.reservedOpNames = ["+", "*", "-"] })
integer = P.integer lexer
letters = P.identifier lexer
parens = P.parens lexer
reservedOp = P.reservedOp lexer

fmterm :: Parser MR
fmterm = do
  str  <- option "" letters
  coef <- option 1 integer
  return $ FreeMod [(coef, str)]

fmparens :: Parser MR
fmparens = parens fmexpr <|> fmterm <?> "term"

fmexpr :: Parser MR
fmexpr = buildExpressionParser table fmparens <?> "expression"
  where
    table = [[binop "*" (*) AssocLeft],
             [binop "+" (+) AssocLeft, binop "-" (-) AssocLeft]]
    unary s op = Prefix (reservedOp s >> return op)
    binop s op assoc = Infix (reservedOp s >> return op <?> "operator") assoc
