\begin{code}
module CKMachine where

import qualified AbstractSyntax as S
import qualified IntegerArithmetic as I

data Cont  =  MachineTerminate
           |  Fun              S.Term Cont -- where Term is a value
           |  Arg              S.Term Cont
           |  If               S.Term S.Term Cont
           |  Fix              Cont
           |  Let              S.Var S.Term Cont
           |  Plus1            S.Term Cont
           |  Plus2            S.Term Cont 
           |  Minus1           S.Term Cont
           |  Minus2           S.Term Cont 
           |  Times1           S.Term Cont
           |  Times2           S.Term Cont 
           |  Div1             S.Term Cont
           |  Div2             S.Term Cont
           |  Nand1            S.Term Cont
           |  Nand2            S.Term Cont 
           |  Eq1              S.Term Cont
           |  Eq2              S.Term Cont 
           |  Lt1              S.Term Cont
           |  Lt2              S.Term Cont          

ckMachineStep :: (S.Term, Cont) -> Maybe (S.Term, Cont)
ckMachineStep (t, k) = case t of
  S.App t1 t2          -> Just (t1, Arg t2 k)
  S.If t1 t2 t3        -> Just (t1, If t2 t3 k)
  S.Fix t1             -> Just (t1, Fix k)
  S.Let x t1 t2        -> Just (t1, Let x t2 k)
  S.IntAdd t1 t2       -> Just (t1, Plus1 t2 k)
  S.IntSub t1 t2       -> Just (t1, Minus1 t2 k)
  S.IntMul t1 t2       -> Just (t1, Times1 t2 k)
  S.IntDiv t1 t2       -> Just (t1, Div1 t2 k)
  S.IntNand t1 t2      -> Just (t1, Nand1 t2 k)
  S.IntEq t1 t2        -> Just (t1, Eq1 t2 k)
  S.IntLt t1 t2        -> Just (t1, Lt1 t2 k)
  otherwise -> if (S.isValue t) then ckContHelp (t,k) else Nothing

ckContHelp :: (S.Term, Cont) -> Maybe (S.Term, Cont)
ckContHelp (t, k) = case k of
  MachineTerminate -> Nothing
  Fun (S.Abs x _ t12) k'        
                   -> Just ((S.subst x t t12), k')
  Arg t2 k'        -> Just (t2, Fun t k')
  If t2 t3 k'      
    | t==S.Tru     -> Just (t2, k')
    | t==S.Fls     -> Just (t3, k')
    | otherwise    -> Nothing 
  Fix k'           -> fixHelper (S.Fix t, k')
  Let x t2 k'      -> Just ((S.subst x t t2), k')
  Plus1 t2 k'      -> Just (t2, Plus2 t k')
  Plus2 v1 k'      -> binaryOpHelp ((S.IntAdd v1 t), k') 
  Minus1 t2 k'     -> Just (t2, Minus2 t k')
  Minus2 v1 k'     -> binaryOpHelp ((S.IntSub v1 t), k') 
  Times1 t2 k'     -> Just (t2, Times2 t k')
  Times2 v1 k'     -> binaryOpHelp ((S.IntMul v1 t), k') 
  Div1 t2 k'       -> Just (t2, Div2 t k')
  Div2 v1 k'       -> binaryOpHelp ((S.IntDiv v1 t), k') 
  Nand1 t2 k'      -> Just (t2, Nand2 t k')
  Nand2 v1 k'      -> binaryOpHelp ((S.IntNand v1 t), k') 
  Eq1 t2 k'        -> Just (t2, Eq2 t k')
  Eq2 v1 k'        -> binaryOpHelp ((S.IntEq v1 t), k') 
  Lt1 t2 k'        -> Just (t2, Lt2 t k')
  Lt2 v1 k'        -> binaryOpHelp ((S.IntLt v1 t), k')
  otherwise        -> Nothing 

fixHelper:: (S.Term, Cont) -> Maybe(S.Term, Cont)
fixHelper (t@(S.Fix (S.Abs x y t1)), k) = Just ((S.subst x t t1), k)
fixHelper ( _ , k)                      = Nothing

binaryOpHelp::(S.Term, Cont) -> Maybe(S.Term, Cont)
binaryOpHelp (t, k) = case t of 
  S.IntAdd (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intAdd t1 t2), k)
  S.IntSub (S.IntConst t1) (S.IntConst t2)
    -> Just (S.IntConst (I.intSub t1 t2), k)
  S.IntMul (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intMul t1 t2), k)
  S.IntDiv (S.IntConst t1) (S.IntConst t2)
    -> Just (S.IntConst (I.intDiv t1 t2), k)
  S.IntNand (S.IntConst t1) (S.IntConst t2) 
    -> Just (S.IntConst (I.intNand t1 t2), k)
  S.IntEq (S.IntConst t1) (S.IntConst t2)
    -> Just ((if (I.intEq t1 t2) then S.Tru else S.Fls), k)
  S.IntLt (S.IntConst t1) (S.IntConst t2) 
    -> Just ((if (I.intLt t1 t2) then S.Tru else S.Fls), k)
  otherwise
    -> Nothing

ckMachineEvalHelp ::(S.Term, Cont) -> (S.Term, Cont)
ckMachineEvalHelp (t, k) =
  case ckMachineStep (t, k) of
    Just t' -> ckMachineEvalHelp t'
    Nothing -> (t,k) 

ckMachineEval :: S.Term -> S.Term
ckMachineEval t = fst (ckMachineEvalHelp (t, MachineTerminate))
\end{code}