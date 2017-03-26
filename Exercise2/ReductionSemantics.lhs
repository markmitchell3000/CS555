\begin{code}

module ReductionSemantics where
import qualified AbstractSyntax as S
import qualified EvaluationContext as E
import qualified IntegerArithmetic as I

makeEvalContext :: S.Term -> Maybe (S.Term, E.Context)
makeEvalContext t = case t of

      S.App (S.Abs x tau11 t12) t2
        | S.isValue t2 		-> Just (t, E.Hole)
		
      S.App t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just (t2', c2) 	-> Just (t2', (E.AppV t1 c2))
			_              	-> Nothing
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just (t1', (E.AppT c1 t2))
			_             	-> Nothing

      S.If (S.Fls) t2 t3 	-> Just (t, E.Hole)
      S.If (S.Tru) t2 t3 	-> Just (t, E.Hole)
      S.If t1 t2 t3 -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just (t1', (E.If c1 t2 t3))
			_             	-> Nothing
	  
      S.IntAdd t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
            Just(t2', c2) 	-> Just(t2', (E.IntAddV t1 c2))
            Nothing       	-> Just(t, E.Hole)    
        | otherwise    -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.IntAddT c1 t2))
			_             	-> Nothing
                               
      S.IntSub t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just(t2', c2) 	-> Just(t2', (E.IntSubV t1 c2))
			Nothing 	  	-> Just(t, E.Hole)      
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.IntSubT c1 t2))
			_             	-> Nothing
                            
      S.IntMul t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just(t2', c2) 	-> Just(t2', (E.IntMulV t1 c2))
			Nothing       	-> Just(t, E.Hole)                
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.IntMulT c1 t2))
			_             	-> Nothing
                            
      S.IntDiv t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just(t2', c2) 	-> Just(t2', (E.IntDivV t1 c2))
			Nothing 		-> Just(t, E.Hole)                  
        | otherwise -> case makeEvalContext t1 of
            Just(t1', c1) 	-> Just(t1', (E.IntDivT c1 t2))
            _             	-> Nothing
                            
      S.IntNand t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just(t2', c2) 	-> Just(t2', (E.IntNandV t1 c2))
			Nothing 		-> Just(t, E.Hole)
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.IntNandT c1 t2))
			_             	-> Nothing
                               
      S.IntEq t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just(t2', c2) 	-> Just(t2', (E.IntEqV t1 c2))
			Nothing 		-> Just(t, E.Hole)
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.IntEqT c1 t2))
			_ 				-> Nothing
                            
      S.IntLt t1 t2
        | S.isValue t1 -> case makeEvalContext t2 of
			Just(t2', c2) 	-> Just(t2', (E.IntLtV t1 c2))
			Nothing 		-> Just(t, E.Hole)
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.IntLtT c1 t2))
			_             	-> Nothing
                            
      S.Let x t1 t2
        | S.isValue t1 		-> Just (t, E.Hole)
        | otherwise -> case makeEvalContext t1 of
			Just(t1', c1) 	-> Just(t1', (E.LetT x c1 t2))
			_             	-> Nothing
                            
      S.Fix (S.Abs x tau11 t12) -> Just (t, E.Hole)
      S.Fix t -> case makeEvalContext t of
		Just(t', c1) 		-> Just(t', E.Fix c1)
		_           		-> Nothing
                      
      _ 					-> Nothing

      
makeContractum :: S.Term -> S.Term
makeContractum t = case t of
	S.App (S.Abs x tau11 t12) t2 				-> S.subst x t2 t12
	S.If (S.Tru) t2 t3 							-> t2
	S.If (S.Fls) t2 t3 							-> t3
	S.IntAdd (S.IntConst n1) (S.IntConst n2) 	-> S.IntConst (I.intAdd n1 n2)
	S.IntSub (S.IntConst n1) (S.IntConst n2) 	-> S.IntConst (I.intSub n1 n2)
	S.IntMul (S.IntConst n1) (S.IntConst n2) 	-> S.IntConst (I.intMul n1 n2)
	S.IntDiv (S.IntConst n1) (S.IntConst n2) 	-> S.IntConst (I.intDiv n1 n2)
	S.IntNand (S.IntConst n1) (S.IntConst n2) 	-> S.IntConst (I.intNand n1 n2)
	S.IntLt (S.IntConst n1) (S.IntConst n2) 	-> if I.intLt n1 n2 then S.Tru else S.Fls
	S.IntEq (S.IntConst n1) (S.IntConst n2) 	-> if I.intEq n1 n2 then S.Tru else S.Fls
	S.Let x t1 t2 								-> S.subst x t1 t2
	S.Fix (S.Abs x tau11 t12) 					-> S.subst x (S.Fix (S.Abs x tau11 t12)) t12

  
textualMachineStep :: S.Term -> Maybe S.Term
textualMachineStep t = case makeEvalContext t of
       Just(t', c) 			-> Just (E.fillWithTerm c (makeContractum t'))
       Nothing     			-> Nothing
   
textualMachineEval :: S.Term -> S.Term
textualMachineEval t =  case textualMachineStep t of
       Just t' 				-> textualMachineEval t'
       Nothing 				-> t

\end{code}
