\begin{code}

module ReductionSemantics where
import qualified AbstractSyntax as S
import qualified EvaluationContext as E
import qualified IntegerArithmetic as I


makeEvalContext :: S.Term -> Maybe (S.Term, E.Context)
makeEvalContext t = case t of

      S.App (S.Abs x tau11 t12) t2
        | S.isValue t2      -> Just (t, E.Hole)
        
      S.App t1 t2
        | S.isValue t1  -> nextEC(t2, (E.AppV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.AppT E.Hole t2))

      S.If (S.Fls) t2 t3    -> Just (t, E.Hole)
      S.If (S.Tru) t2 t3    -> Just (t, E.Hole)
      S.If t1 t2 t3         -> nextEC(t1, (E.If E.Hole t2 t3))
      
      S.IntAdd (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)
      S.IntAdd t1 t2
        | S.isValue t1  -> nextEC(t2, (E.IntAddV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.IntAddT E.Hole t2))
            
      S.IntSub (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)                    
      S.IntSub t1 t2
        | S.isValue t1  -> nextEC (t2, (E.IntSubV t1 E.Hole))
        | otherwise     -> nextEC (t1, (E.IntSubT E.Hole t2))
            
      S.IntMul (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)                                     
      S.IntMul t1 t2
        | S.isValue t1  -> nextEC(t2, (E.IntMulV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.IntMulT E.Hole t2))
            
      S.IntDiv (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)                                                
      S.IntDiv t1 t2
        | S.isValue t1  -> nextEC(t2, (E.IntDivV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.IntDivT E.Hole t2))
            
      S.IntNand (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)                                            
      S.IntNand t1 t2
        | S.isValue t1  -> nextEC(t2, (E.IntNandV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.IntNandT E.Hole t2))
            
      S.IntEq (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)                                
      S.IntEq t1 t2
        | S.isValue t1  -> nextEC(t2, (E.IntEqV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.IntEqT E.Hole t2))
            
      S.IntLt (S.IntConst t1) (S.IntConst t2) -> Just (t, E.Hole)                      
      S.IntLt t1 t2
        | S.isValue t1  -> nextEC(t2, (E.IntLtV t1 E.Hole))
        | otherwise     -> nextEC(t1, (E.IntLtT E.Hole t2))
                            
      S.Let x t1 t2
        | S.isValue t1      -> Just (t, E.Hole)
        | otherwise ->  nextEC(t1, (E.LetT x E.Hole t2))
                            
      S.Fix (S.Abs x tau11 t12) -> Just (t, E.Hole)
      S.Fix t -> Just(t, E.Fix E.Hole)
                      
      _                     -> Nothing

nextEC :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
nextEC (t,c) = do 
  (t',c') <- makeEvalContext t
  return(t', E.fillWithContext c c')

makeContractum :: S.Term -> S.Term
makeContractum t = case t of
    S.App (S.Abs x tau11 t12) t2                -> S.subst x t2 t12
    S.If (S.Tru) t2 t3                          -> t2
    S.If (S.Fls) t2 t3                          -> t3
    S.IntAdd (S.IntConst n1) (S.IntConst n2)    -> S.IntConst (I.intAdd n1 n2)
    S.IntSub (S.IntConst n1) (S.IntConst n2)    -> S.IntConst (I.intSub n1 n2)
    S.IntMul (S.IntConst n1) (S.IntConst n2)    -> S.IntConst (I.intMul n1 n2)
    S.IntDiv (S.IntConst n1) (S.IntConst n2)    -> S.IntConst (I.intDiv n1 n2)
    S.IntNand (S.IntConst n1) (S.IntConst n2)   -> S.IntConst (I.intNand n1 n2)
    S.IntLt (S.IntConst n1) (S.IntConst n2)     -> if (I.intLt n1 n2) then S.Tru else S.Fls
    S.IntEq (S.IntConst n1) (S.IntConst n2)     -> if (I.intEq n1 n2) then S.Tru else S.Fls
    S.Let x t1 t2                               -> S.subst x t1 t2
    S.Fix (S.Abs x tau11 t12)                   -> S.subst x (S.Fix (S.Abs x tau11 t12)) t12

  
textualMachineStep :: S.Term -> Maybe S.Term
textualMachineStep t = case makeEvalContext t of
       Just(t', c)          -> Just (E.fillWithTerm c (makeContractum t'))
       _                    -> Nothing
   
textualMachineEval :: S.Term -> S.Term
textualMachineEval t =  case textualMachineStep t of
       Just t'              -> textualMachineEval t'
       _                    -> t


\end{code}
