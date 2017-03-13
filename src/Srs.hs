module Srs where

import Data.List
import Data.Maybe

type Rule = (String, String)
type SRS = [Rule]

data Red = Red String String Rule deriving (Eq, Show)

data Tree = Branch Red [Tree] deriving (Eq, Show)

data Crit = Crit String Rule Rule deriving (Eq, Show)

hd :: String -> Tree
hd w = Branch (Red "" "" ("", w)) []

one rd = Branch rd []

height :: Tree -> Int
height (Branch rd ts) = 1 + maximum (map height ts)

leaves :: Tree -> [Red]
leaves (Branch rd []) = [rd]
leaves (Branch rd ts) = ts >>= leaves

red' :: Rule -> (String, String) -> Maybe Red
red' (r, s) (w', w)
  | r `isPrefixOf` w = Just $ Red w' (drop (length r) w) (r, s)
  | otherwise        = Nothing

red :: Rule -> String -> [Red]
red rel w = mapMaybe (red' rel) $ map (\i -> splitAt i w) [0..length w]

redAll :: SRS -> String -> [Red]
redAll rules w = rules >>= flip red w

redTree :: SRS -> String -> Tree
redTree rules w = redTree' $ hd w
  where
    redTree' :: Tree -> Tree
    redTree' (Branch rd []) = let l = map one $ redAll rules $ repl rd in
                              Branch rd $ map redTree' l
    redTree' (Branch rd ts) = Branch rd $ map redTree' ts

orig :: Red -> String
orig (Red u v (r, _)) = u ++ r ++ v

repl :: Red -> String
repl (Red u v (_, s)) = u ++ s ++ v

isIrr :: SRS -> String -> Bool
isIrr rules w = redAll rules w == []

isRedble :: SRS -> String -> Bool
isRedble rules w = not $ isIrr rules w

prefixes :: String -> [String]
prefixes w = map (flip take w) [1..length w - 1]

isRMinimal :: SRS -> String -> Bool
isRMinimal rules w = isRedble rules w && all (isIrr rules) (prefixes w)

children :: SRS -> String -> [String]
children rels w = nub $ map repl $ redAll rels w

isReduced :: SRS -> Bool
isReduced rules = all (\(r, s) -> isIrr rules s && not (any (isInfixOf r) (map fst rules))) rules

remOverlap' :: SRS -> SRS -> SRS
remOverlap' [] rules = rules
remOverlap' ((r,s):rest) rules
  | any (isInfixOf r) (map fst $ rest ++ rules) = remOverlap' rest rules
  | otherwise = remOverlap' rest (rules ++ [(r,s)])

remOverlap :: SRS -> SRS
remOverlap rules = remOverlap' rules []

critPairs' :: Rule -> Rule -> [Crit]
critPairs' (r1, s1) (r2, s2) = nub $ [1..length r1 - 1] >>= (\i -> critPairs'' $ splitAt i r1)
  where
    critPairs'' (r11, r12) = (if r12 `isPrefixOf` r2 then [Crit r12 (r1, s1) (r2, s2)] else [])
                               ++ if r11 `isSuffixOf` r2 then [Crit r11 (r2, s2) (r1, s1)] else []

critPairs :: SRS -> [Crit]
critPairs [] = []
critPairs l@((r,s):rest) = (l >>= critPairs' (r, s)) ++ critPairs rest

critStr :: Crit -> String
critStr (Crit r (r1, _) (r2, _)) = r1 ++ drop (length r) r2

normalForm :: SRS -> String -> String
normalForm rules w = repl $ head $ leaves $ redTree rules w

normalForms :: SRS -> String -> [String]
normalForms rules w = map repl $ leaves $ redTree rules w

confluent :: SRS -> String -> Bool
confluent rules w = length (nub $ map repl $ leaves $ redTree rules w) == 1

isConfl :: SRS -> Bool
isConfl rules = and $ map (confluent rules . critStr) $ critPairs rules

ordRule :: Rule -> Rule -> Ordering
ordRule (r1, s1) (r2, s2) = compare (length r1 - length s1) (length r2 - length s2)

ordCrit :: Crit -> Crit -> Ordering
ordCrit (Crit _ (r1, s1) (r2, s2)) (Crit _ (r1', s1') (r2', s2')) =
  compare (length r1 - length s1 + length r2 - length s2) (length r1' - length s1' + length r2' - length s2')

essCritPairs' :: SRS -> Rule -> Rule -> [Crit]
essCritPairs' rules (r1, s1) (r2, s2) = nub $ [1..length r1 - 1] >>= (\i -> critPairs'' $ splitAt i r1)
  where
    critPairs'' (r11, r12) = (if r12 `isPrefixOf` r2 && intersect (normalForms rules $ s1 ++ drop (length r12) r2) (normalForms rules $ r11 ++ s2) == []
                                  then [Crit r12 (r1, s1) (r2, s2)]
                                  else [])
                             ++ if r11 `isSuffixOf` r2 && intersect (normalForms rules $ s2 ++ r12) (normalForms rules $ take (length r2 - length r11) r2 ++ r1) == []
                                  then [Crit r11 (r2, s2) (r1, s1)]
                                  else []

essCritPairs'' :: SRS -> SRS -> [Crit]
essCritPairs'' _ [] = []
essCritPairs'' rules l@((r,s):rest) = (l >>= essCritPairs' rules (r, s)) ++ essCritPairs'' rules rest

essCritPairs :: SRS -> [Crit]
essCritPairs rules = essCritPairs'' rules rules

completion' :: SRS -> Crit -> SRS
completion' rules (Crit r (r1, s1) (r2, s2))
  | length w1 >= length w2 = insertBy ordRule (w1, w2) rules
  | otherwise = insertBy ordRule (w2, w1) rules
  where
    w1 = normalForm rules (take (length r1 - length r) r1 ++ s2)
    w2 = normalForm rules (s1 ++ drop (length r) r2)

completion'' :: SRS -> [Crit] -> SRS
completion'' rules [] = rules
completion'' rules (c:rest) = completion $ completion'' (completion' rules c) rest

completion :: SRS -> SRS
completion rules
  | ecps == [] = rules
  | otherwise = completion'' ordered ecps
  where
    ordered = sortBy ordRule rules
    ecps = sortBy ordCrit $ essCritPairs ordered
