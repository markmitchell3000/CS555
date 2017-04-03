\begin{code}
module CCMachine where

import qualified AbstractSyntax as S
import qualified EvaluationContext as E
import qualified IntegerArithmetic as I

ccMachineStep :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
ccMachineStep (t, c) = case t of
  S.App t1 t2
    | not (S.isValue t1) 
      -> Just (t1, E.fillWithContext c (E.AppT E.Hole t2))       {-cc1-}
    | S.isValue t1 && not (S.isValue t2)      
      -> Just (t2, E.fillWithContext c (E.AppV t1 E.Hole))       {-cc2-}
  S.App (S.Abs x _ t12) t2 -> Just (S.subst x t2 t12, c)         {-ccbeta-}

  S.If (S.Tru) t1 t2       -> Just (t1, c)
  S.If (S.Fls) t1 t2       -> Just (t2, c)
  S.If t1 t2 t3            -> Just (t1, E.fillWithContext c (E.If E.Hole t2 t3))

  S.Fix (S.Abs x y t1)     -> Just ((S.subst x t t1), c)
  S.Fix t1                 -> Just (t1, E.fillWithContext c (E.Fix E.Hole))

  S.Let x t1 t2 
    | S.isValue t1 -> Just ((S.subst x t1 t2), c)
    | otherwise    -> Just (t1, E.fillWithContext c (E.LetT x E.Hole t2))

  S.IntAdd (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intAdd t1 t2), c)
  S.IntAdd t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntAddV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntAddT E.Hole t2))

  S.IntSub (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intSub t1 t2), c)
  S.IntSub t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntSubV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntSubT E.Hole t2))

  S.IntMul (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intMul t1 t2), c)
  S.IntMul t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntMulV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntMulT E.Hole t2))

  S.IntDiv (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intDiv t1 t2), c)
  S.IntDiv t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntDivV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntDivT E.Hole t2))

  S.IntNand (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intNand t1 t2), c)
  S.IntNand t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntNandV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntNandT E.Hole t2))

  S.IntEq (S.IntConst t1) (S.IntConst t2) 
    -> Just ((if (I.intEq t1 t2) then S.Tru else S.Fls), c)
  S.IntEq t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntEqV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntEqT E.Hole t2))

  S.IntLt (S.IntConst t1) (S.IntConst t2) 
    -> Just ((if (I.intLt t1 t2) then S.Tru else S.Fls), c)
  S.IntLt t1 t2 
    | S.isValue t1 -> Just (t2, E.fillWithContext c (E.IntLtV t1 E.Hole))
    | otherwise    -> Just (t1, E.fillWithContext c (E.IntLtT E.Hole t2))

  otherwise -> if (S.isValue t) then (fillTermHelper1 (t,c) E.Hole) else Nothing

fillTermHelper1 :: (S.Term, E.Context)-> E.Context -> Maybe (S.Term, E.Context)
fillTermHelper1 (t, c) c1 = case c of
  E.Hole -> Nothing
  E.AppT t1 t2     -> fTH2 (t, c, c1, t1, (E.AppT E.Hole t2))
  E.AppV t1 t2     -> fTH2 (t, c, c1, t2, (E.AppV t1 E.Hole))
  E.If t1 t2 t3    -> fTH2 (t, c, c1, t1, (E.If E.Hole t2 t3))
  E.Fix t1         -> fTH2 (t, c, c1, t1, (E.Fix E.Hole))
  E.LetT x t1 t2   -> fTH2 (t, c, c1, t1, (E.LetT x E.Hole t2))
  E.IntAddV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntAddV t1 E.Hole))
  E.IntAddT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntAddT E.Hole t2))
  E.IntSubV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntSubV t1 E.Hole))
  E.IntSubT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntSubT E.Hole t2))
  E.IntMulV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntMulV t1 E.Hole))
  E.IntMulT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntMulT E.Hole t2))
  E.IntDivV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntDivV t1 E.Hole))
  E.IntDivT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntDivT E.Hole t2))
  E.IntNandV t1 t2 -> fTH2 (t, c, c1, t2, (E.IntNandV t1 E.Hole))
  E.IntNandT t1 t2 -> fTH2 (t, c, c1, t1, (E.IntNandT E.Hole t2))
  E.IntEqV t1 t2   -> fTH2 (t, c, c1, t2, (E.IntEqV t1 E.Hole))
  E.IntEqT t1 t2   -> fTH2 (t, c, c1, t1, (E.IntEqT E.Hole t2))
  E.IntLtV t1 t2   -> fTH2 (t, c, c1, t2, (E.IntLtV t1 E.Hole))
  E.IntLtT t1 t2   -> fTH2 (t, c, c1, t1, (E.IntLtT E.Hole t2))
  otherwise        -> Nothing

-- This function takes a term t and a context c, this context may fill a hole in
-- context c1, context c2 is the nested context in c if c2 is not a hole to be
-- filled by t then we recur and c3 pererves the structure of c at that level, 
-- with a hole where c2 is taken from.
fTH2::(S.Term,E.Context,E.Context,E.Context,E.Context)-> Maybe(S.Term,E.Context)
fTH2 (t,c,c1,c2,c3) = if (isHole c2) then Just (E.fillWithTerm c t, c1)
                      else (fillTermHelper1 (t, c2) (E.fillWithContext c1 c3))
  
isHole :: E.Context -> Bool
isHole E.Hole = True
isHole _      = False

ccMachineEvalHelp ::(S.Term, E.Context) -> (S.Term, E.Context)
ccMachineEvalHelp (t, c) =
  case ccMachineStep (t, c) of
    Just t' -> ccMachineEvalHelp t'
    Nothing -> (t,c)

ccMachineEval :: S.Term -> S.Term
ccMachineEval t = fst (ccMachineEvalHelp (t, E.Hole))

\end{code}