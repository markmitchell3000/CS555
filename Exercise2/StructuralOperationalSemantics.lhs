\begin{code}
module StructuralOperationalSemantics where

import Data.List
import qualified AbstractSyntax as S
import qualified IntegerArithmetic as I

termToInt:: S.Term -> Integer
termToInt (S.IntConst x) = x
termToInt _              = error ("Non integer in arithmetic application")

justVal:: Maybe S.Term -> S.Term
justVal (Just x) = x
justVal _ = error ("incorrect use of justVal")

eval1 :: S.Term -> Maybe S.Term
eval1 t = case t of
  S.App (S.Abs x tau11 t12) t2
    |  S.isValue t2 -> Just (S.subst x t2 t12)
    |  otherwise    -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.App (S.Abs x tau11 t12) (justVal newT2))
  S.App t1 t2  
    |  S.isValue t1 -> Nothing
    |  otherwise -> let newT1 = (eval1 t1)
                       in if (newT1==Nothing) then Nothing
                            else Just (S.App (justVal newT1) t2)
  S.If t1 t2 t3
    |  not(S.isValue t1) -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.If (justVal newT1) t2 t3)
    |  t1==S.Tru -> Just t2
    |  t1==S.Fls -> Just t3
    |  otherwise -> Nothing
  S.Fix (S.Abs x _ t1) -> Just (S.subst x (S.Fix (S.Abs x _ t1)) t1)
  S.Fix t -> if (eval t) == Nothing then Nothing else Just (S.Fix (eval t))
  S.Let x t1 t2 
    | S.isValue t1 -> Just (S.subst x t1 t2)
    | otherwise -> let newT1 = (eval1 t1)
                       in if (newT1==Nothing) then Nothing
                            else Just (S.Let x (justVal newT1) t2)
  S.IntAdd t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntAdd (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntAdd t1 (justVal newT2))
    |  otherwise -> Just(S.IntConst (I.intAdd (termToInt t1) (termToInt t2)))
  S.IntSub t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntSub (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntSub t1 (justVal newT2))
    |  otherwise -> Just(S.IntConst (I.intSub (termToInt t1) (termToInt t2)))
  S.IntMul t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntMul (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntMul t1 (justVal newT2))
    |  otherwise -> Just(S.IntConst (I.intMul (termToInt t1) (termToInt t2)))
  S.IntDiv t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntDiv (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntDiv t1 (justVal newT2))
    |  otherwise -> Just(S.IntConst (I.intDiv (termToInt t1) (termToInt t2)))
  S.IntNand t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntNand (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntNand t1 (justVal newT2))
    |  otherwise -> Just(S.IntConst (I.intNand (termToInt t1) (termToInt t2))) 
  S.IntEq t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntEq (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntEq t1 (justVal newT2))
    |  otherwise -> if(I.intEq (termToInt t1) (termToInt t2)) 
                      then Just S.Tru else Just S.Fls
  S.IntLt t1 t2
    |  not(S.isValue t1)  -> 
       let newT1 = (eval1 t1)
          in if (newT1==Nothing) then Nothing 
             else Just (S.IntLt (justVal newT1) t2)
    |  not(S.isValue t2)  -> 
       let newT2 = (eval1 t2)
          in if (newT2==Nothing) then Nothing 
             else Just (S.IntLt t1 (justVal newT2))
    |  otherwise -> if(I.intLt (termToInt t1) (termToInt t2))
                      then Just S.Tru else Just S.Fls
  S.ParTerm t  -> (eval1 t)
  S.Tru        -> Nothing
  S.Fls        -> Nothing
  S.IntConst _ -> Nothing
  S.Var _      -> Nothing
  S.Abs _ _ _  -> Nothing


eval :: S.Term -> S.Term
eval t =
  case eval1 t of
    Just t' -> eval t'
    Nothing -> t

\end{code}