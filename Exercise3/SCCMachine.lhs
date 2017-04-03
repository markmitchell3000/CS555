\begin{code}
module SCCMachine where

import qualified AbstractSyntax as S
import qualified EvaluationContext as E
import qualified IntegerArithmetic as I

sccMachineStep :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
sccMachineStep (t, c) = case t of
  S.App t1 t2          -> Just (t1, E.fillWithContext c (E.AppT E.Hole t2))
  S.If t1 t2 t3        -> Just (t1, E.fillWithContext c (E.If E.Hole t2 t3))
  S.Fix t1             -> Just (t1, E.fillWithContext c (E.Fix E.Hole))
  S.Let x t1 t2        -> Just (t1, E.fillWithContext c (E.LetT x E.Hole t2))
  S.IntAdd t1 t2       -> Just (t1, E.fillWithContext c (E.IntAddT E.Hole t2))
  S.IntSub t1 t2       -> Just (t1, E.fillWithContext c (E.IntSubT E.Hole t2))
  S.IntMul t1 t2       -> Just (t1, E.fillWithContext c (E.IntMulT E.Hole t2))
  S.IntDiv t1 t2       -> Just (t1, E.fillWithContext c (E.IntDivT E.Hole t2))
  S.IntNand t1 t2      -> Just (t1, E.fillWithContext c (E.IntNandT E.Hole t2))
  S.IntEq t1 t2        -> Just (t1, E.fillWithContext c (E.IntEqT E.Hole t2))
  S.IntLt t1 t2        -> Just (t1, E.fillWithContext c (E.IntLtT E.Hole t2))

  otherwise -> if (S.isValue t) then (fillTermHelper1 (t,c) E.Hole) else Nothing

-- Similar to the one in the CC machine but this handles cases of flipping 
-- contexts like E.AppT E.Hole t2 for E.AppV t1 E.Hole where t1 is a value this
-- also handles cases where terms can be applied such as addition or application
-- this context is removed and used to create a new value, leaving a E.Hole in 
-- since that particular redux is complete. 
fillTermHelper1 :: (S.Term, E.Context)-> E.Context -> Maybe (S.Term, E.Context)
fillTermHelper1 (t, c) c1 = case c of
  E.Hole -> Nothing
  E.AppT E.Hole t2 -> Just (t2, E.fillWithContext c1 (E.AppV t E.Hole))
  E.AppT t1 t2     -> fTH2 (t, c, c1, t1, (E.AppT E.Hole t2))
  E.AppV (S.Abs x _ t12) E.Hole 
    -> Just ((S.subst x t t12), c1)
  E.AppV _ E.Hole  -> Nothing
  E.AppV t1 t2     -> fTH2 (t, c, c1, t2, (E.AppV t1 E.Hole))
  E.If E.Hole t2 t3
    | t==S.Tru     -> Just (t2, c1)
    | t==S.Fls     -> Just (t3, c1)
    | otherwise    -> Nothing
  E.If t1 t2 t3    -> fTH2 (t, c, c1, t1, (E.If E.Hole t2 t3))
  E.Fix E.Hole     -> fixHelper (S.Fix t, c1)
  E.Fix t1         -> fTH2 (t, c, c1, t1, (E.Fix E.Hole))
  E.LetT x E.Hole t2 
                   -> Just ((S.subst x t t2), c1)
  E.LetT x t1 t2   -> fTH2 (t, c, c1, t1, (E.LetT x E.Hole t2))
  E.IntAddV t1 E.Hole 
                   -> binaryOpHelp ((S.IntAdd t1 t), c1)
  E.IntAddV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntAddV t1 E.Hole))
  E.IntAddT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntAddV t E.Hole))
  E.IntAddT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntAddT E.Hole t2))
  E.IntSubV t1 E.Hole 
                   -> binaryOpHelp ((S.IntSub t1 t), c1)
  E.IntSubV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntSubV t1 E.Hole))
  E.IntSubT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntSubV t E.Hole))
  E.IntSubT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntSubT E.Hole t2))
  E.IntMulV t1 E.Hole
                   -> binaryOpHelp ((S.IntMul t1 t), c1) 
  E.IntMulV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntMulV t1 E.Hole))
  E.IntMulT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntMulV t E.Hole))
  E.IntMulT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntMulT E.Hole t2))
  E.IntDivV t1 E.Hole
                   -> binaryOpHelp ((S.IntDiv t1 t), c1)  
  E.IntDivV t1 t2  -> fTH2 (t, c, c1, t2, (E.IntDivV t1 E.Hole))
  E.IntDivT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntDivV t E.Hole))
  E.IntDivT t1 t2  -> fTH2 (t, c, c1, t1, (E.IntDivT E.Hole t2))
  E.IntNandV t1 E.Hole
                   -> binaryOpHelp ((S.IntNand t1 t), c1)
  E.IntNandV t1 t2 -> fTH2 (t, c, c1, t2, (E.IntNandV t1 E.Hole))
  E.IntNandT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntNandV t E.Hole))
  E.IntNandT t1 t2 -> fTH2 (t, c, c1, t1, (E.IntNandT E.Hole t2))
  E.IntEqV t1 E.Hole
                   -> binaryOpHelp ((S.IntEq t1 t), c1)
  E.IntEqV t1 t2   -> fTH2 (t, c, c1, t2, (E.IntEqV t1 E.Hole))
  E.IntEqT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntEqV t E.Hole))
  E.IntEqT t1 t2   -> fTH2 (t, c, c1, t1, (E.IntEqT E.Hole t2))
  E.IntLtV t1 E.Hole
                   -> binaryOpHelp ((S.IntLt t1 t), c1)
  E.IntLtV t1 t2   -> fTH2 (t, c, c1, t2, (E.IntLtV t1 E.Hole))
  E.IntLtT E.Hole t2 
                   -> Just (t2, E.fillWithContext c1 (E.IntLtV t E.Hole))
  E.IntLtT t1 t2   -> fTH2 (t, c, c1, t1, (E.IntLtT E.Hole t2))
  otherwise        -> Nothing

-- This function takes a term t and a context c, this context may fill a hole in
-- context c1, context c2 is the nested context in c if c2 is not a hole to be
-- filled by t then we recur and c3 pererves the structure of c at that level, 
-- with a hole where c2 is taken from.
fTH2::(S.Term,E.Context,E.Context,E.Context,E.Context)-> Maybe(S.Term,E.Context)
fTH2 (t,c,c1,c2,c3) = if (isHole c2) then Just (E.fillWithTerm c t, c1)
                      else (fillTermHelper1 (t, c2) (E.fillWithContext c1 c3))

fixHelper:: (S.Term, E.Context) -> Maybe(S.Term, E.Context)
fixHelper (t@(S.Fix (S.Abs x y t1)), c) = Just ((S.subst x t t1), c)
fixHelper ( _ , c)                      = Nothing

binaryOpHelp::(S.Term, E.Context) -> Maybe(S.Term, E.Context)
binaryOpHelp (t, c) = case t of 
  S.IntAdd (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intAdd t1 t2), c)
  S.IntSub (S.IntConst t1) (S.IntConst t2)
    -> Just (S.IntConst (I.intSub t1 t2), c)
  S.IntMul (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intMul t1 t2), c)
  S.IntDiv (S.IntConst t1) (S.IntConst t2)
    -> Just (S.IntConst (I.intDiv t1 t2), c)
  S.IntNand (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intNand t1 t2), c)
  S.IntEq (S.IntConst t1) (S.IntConst t2)
    -> Just ((if (I.intEq t1 t2) then S.Tru else S.Fls), c)
  S.IntLt (S.IntConst t1) (S.IntConst t2) 
    -> Just ((if (I.intLt t1 t2) then S.Tru else S.Fls), c)
  otherwise
    -> Nothing

isHole :: E.Context -> Bool
isHole E.Hole = True
isHole _      = False

sccMachineEvalHelp ::(S.Term, E.Context) -> (S.Term, E.Context)
sccMachineEvalHelp (t, c) =
  case sccMachineStep (t, c) of
    Just t' -> sccMachineEvalHelp t'
    Nothing -> (t,c)

sccMachineEval :: S.Term -> S.Term
sccMachineEval t = fst (sccMachineEvalHelp (t, E.Hole))
\end{code}