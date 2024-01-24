module Int where
import GHC.Real
import Data.List
import Data.Maybe
import Control.Applicative

import Types
import Utilities
import Examples

--
-- Universal assumptions/preconditions:
-- 1. All polynomials are in standard form with decreasing
--    powers of x
-- 2. 0 is represented by P [(0, 0)]; P [] is undefined for
--    the purposes of the exercise.
-- 3. All constants will be polynomials of the form
--    [(c, 0)], e.g. logarithms of constants and constant
--    powers will not appear.
-- 4. All computed integrals omit the constant of integration.
--

-------------------------------------------------
-- Part I (13 marks)

std :: Polynomial -> Polynomial
std p = std' (sortBy (\(c1, e1) (c2, e2) -> compare e2 e1) p)
  where
    std' :: Polynomial -> Polynomial
    std' (t1@(c1, e1):t2@(c2, e2):ts)
      | e1 == e2 = (c1 + c2, e1) : std ts
      | e1 > e2 = t1 : std(t2:ts)
      | otherwise = t2 : std (t1:ts)
    std' (t1:ts) = t1 : std ts
    std' _ = []

addP :: Polynomial -> Polynomial -> Polynomial
addP p1 p2 = std ((p1 ++ p2))

mulP :: Polynomial -> Polynomial -> Polynomial
mulP t1 t2
  = std ([(coeff1 * coeff2, exp1 + exp2) | 
              (coeff1, exp1) <- t1, 
              (coeff2, exp2) <- t2]
          )

sumP :: [Polynomial] -> Polynomial
sumP = foldr1 addP

prodP :: [Polynomial] -> Polynomial
prodP = foldr1 mulP

diffT :: Term -> Term
diffT (_, 0) = (0 :% 1, 0)
diffT ((cn :% cd), exp) = (exp * cn % cd, exp - 1)

intT :: Term -> Term
intT ((cn :% cd), exp) = (cn % (cd * newExp), newExp)
  where
    newExp = exp + 1

diffP :: Polynomial -> Polynomial
diffP (t:ts) = diffT t : diffP ts
diffP _ = []

intP :: Polynomial -> Polynomial
intP (t:ts) = intT t : intP ts
intP _ = []

-------------------------------------------------
-- Part II (7 marks)

diffE :: Expr -> Expr
diffE (P ps) = P (diffP ps)
diffE (Add e1 e2) = Add (diffE e1) (diffE e2)
diffE (Mul e1 e2) = Add (Mul e1 (diffE e2)) (Mul (diffE e1) e2)
diffE (Pow e1 r@(n :% d)) = Mul (toExpr r) (Pow e1 ((n - d) % d))
diffE (Log e1) = Pow e1 (-1 % 1)

--
-- Given
--
toExpr :: Rational -> Expr
toExpr n = P [(n, 0)]

isConstant :: Expr -> Bool
isConstant (P [(_, 0)]) = True
isConstant _ = False

simplifiedDiff :: Expr -> Expr
simplifiedDiff = simplify . diffE

printDiff :: Expr -> IO ()
printDiff = prettyPrint . simplifiedDiff

-------------------------------------------------
-- Part III (10 marks)

intE :: Expr -> Maybe Expr
intE (P ps) = Just (P (intP ps))
intE (Add e1 e2) = do
                      e1' <- intE e1
                      e2' <- intE e2
                      return (Add e1' e2')
intE (Mul e1 e2)
  --  Check constants
  | isConstant e1 = do
                      e2' <- intE e2
                      return (Mul e1 e2')
  | isConstant e2 = do
                      e1' <- intE e1
                      return (Mul e1' e2)
  -- Check id function
  | diffE e2 == e1 = Just (Mul (Pow e2 (2 % 1)) (toExpr (1 % 2)))
  | diffE e1 == e2 = Just (Mul (Pow e1 (2 % 1)) (toExpr (1 % 2)))
  -- Use reverse chain rule
  | otherwise = applyICR e1 e2
intE (Pow e1 (-1 :% 1)) = Just (Log e1)
intE (Pow e1 (nn :% nd)) = Just (Mul  (Pow x newN) 
                                      (Pow (toExpr newN) (-1 % 1)))
  where
    newN = (nn + nd) % nd
intE (Log e1) = Just (Mul e1 (Add (Log e1) (toExpr (negate 1))))

subBackIn :: Expr -> Expr -> Expr
subBackIn e1 (P ((coeff, e):ps)) = Mul (toExpr coeff) (Pow e1 (toRational e))
subBackIn e1 (Log e2) = Log (subBackIn e1 e2)
subBackIn e1 (Add e2 e3) = Add (subBackIn e1 e2) (subBackIn e1 e3)
subBackIn e1 (Mul e2 e3) = Mul (subBackIn e1 e2) (subBackIn e1 e3)
subBackIn e1 (Pow e2 n) = Pow (subBackIn e1 e2) n

applyICR :: Expr -> Expr -> Maybe Expr
applyICR e1 (Pow e2 n)
  | e2' == e1 = do 
                  i <- intE (Pow e2 n)
                  return (Mul (toExpr (denominator f % numerator f)) (subBackIn e2 i))
  | otherwise = Nothing
  where
    (e2', f) = case simplify (diffE e2) of
      (Mul (P ((f', 0):_)) x) -> (x, f')
      otherwise -> (diffE e2, 1)
applyICR e1 (Log e2) 
  | e2' == e1 = do 
                  i <- intE (Log e2)
                  return (Mul (toExpr (denominator f % numerator f)) i)
  | otherwise = Nothing
  where
    (e2', f) = case simplify (diffE e2) of
      (Mul (P ((f', 0):_)) x) -> (x, f')
      otherwise -> (diffE e2, 1)
applyICR e2@(Pow _ n) e1 = applyICR e1 e2
applyICR e2@(Log _) e1 = applyICR e1 e2
applyICR e1 e2 = intE (Mul (Mul e1 (toExpr 1)) e2)

--
-- Given...
--
simplifiedInt :: Expr -> Maybe Expr
simplifiedInt = fmap simplify . intE

printInt :: Expr -> IO ()
printInt e = maybe (putStrLn "Fail") prettyPrint (simplifiedInt e)
