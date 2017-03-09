\begin{code}
module EvaluationContext where
import qualified AbstractSyntax as S
data Context  =  Hole
		|  AppT        	Context S.Term
		|  AppV        	S.Term Context 
		|  If          	Context S.Term S.Term
		|  If          	S.Term Context S.Term
		|  If          	S.Term S.Term Context
		|  IntAdd 		Context S.Term
		|  IntAdd 		S.Term Context
		|  IntSub 		Context S.Term
		|  IntSub 		S.Term Context
		|  IntMul 		Context S.Term
		|  IntMul 		S.Term Context
		|  IntDiv 		Context S.Term
		|  IntDiv 		S.Term Context
		|  IntNand 		Context S.Term
		|  IntNand 		S.Term Context
		|  IntEq 		Context S.Term
		|  IntEq 		S.Term Context
		|  IntLt 		Context S.Term 
		|  IntLt 		S.Term Context
		|  ParTerm 		Context
		|  Fix 			Context
		|  Let 			S.Var Context S.Term
		|  Let 			S.Var S.Term Context

fillWithTerm :: Context -> S.Term -> S.Term
fillWithTerm c t = case c of
		Hole                 	->  t
		AppT c1 t2            	->  S.App (fillWithTerm c1 t) t2
		AppV t1 c2            	->  S.App t1 (fillWithTerm c2 t)
		If c1 t2 t3           	->  S.If (fillWithTerm c1 t) t2 t3
		If t1 c2 t3           	->  S.If t1 (fillWithTerm c2 t) t3
		If t1 t2 c3           	->  S.If t1 t2 (fillWithTerm c3 t)
		IntAdd c1 t2			->  S.IntAdd (fillWithTerm c1 t) t2
		IntAdd t1 c2			->	S.IntAdd t1 (fillWithTerm c2 t)
		IntSub c1 t2			->	S.IntSub (fillWithTerm c1 t) t2
		IntSub t1 c2			->	S.IntSub t1 (fillWithTerm c2 t)
		IntMul c1 t2			->	S.IntMul (fillWithTerm c1 t) t2
		IntMul t1 c2			->	S.IntMul t1 (fillWithTerm c2 t)
		IntDiv c1 t2			->	S.IntDiv (fillWithTerm c1 t) t2
		IntDiv t1 c2			->	S.IntDiv t1 (fillWithTerm c2 t)
		IntNand c1 t2			->	S.IntNand (fillWithTerm c1 t) t2
		IntNand t1 c2			->	S.IntNand t1 (fillWithTerm c2 t)
		IntEq c1 t2				-> 	S.IntEq (fillWithTerm c1 t) t2
		IntEq t1 c2				->	S.IntEq t1 (fillWithTerm c2 t)
		IntLt c1 t2				->	S.IntLt (fillWithTerm c1 t) t2
		IntLt t1 c2				->	S.IntLt t1 (fillWithTerm c2 t)
		ParTerm c1				-> 	S.ParTerm (fillWithTerm c1 t)
		Fix c1					->	S.Fix (fillWithTerm c1 t)
		Let v1 c2 t3			->	S.Let v1 (fillWithTerm c2 t) t3
		Let v1 t2 c3			->	S.Let v1 t2 (fillWithTerm c3 t)

fillWithContext :: Context -> Context -> Context
fillWithContext c c' = case c of
		Hole                  	->  c'
		AppT c1 t2            	->  AppT (fillWithContext c1 c') t2
		AppV t1 c2            	->  AppV t1 (fillWithContext c2 c')
		If c1 t2 t3           	->  If (fillWithContext c1 c') t2 t3
		If t1 c2 t3           	->  If t1 (fillWithContext c2 c')  t3
		If t1 t2 c3           	->  If t1 t2 (fillWithContext c3 c')
		IntAdd c1 t2			->  IntAdd (fillWithContext c1 c') t2
		IntAdd t1 c2			->	IntAdd t1 (fillWithContext c2 c')
		IntSub c1 t2			->	IntSub (fillWithContext c1 c') t2
		IntSub t1 c2			->	IntSub t1 (fillWithContext c2 c')
		IntMul c1 t2			->	IntMul (fillWithContext c1 c') t2
		IntMul t1 c2			->	IntMul t1 (fillWithContext c2 c')
		IntDiv c1 t2			->	IntDiv (fillWithContext c1 c') t2
		IntDiv t1 c2			->	IntDiv t1 (fillWithContext c2 c')
		IntNand c1 t2			->	IntNand (fillWithContext c1 c') t2
		IntNand t1 c2			->	IntNand t1 (fillWithContext c2 c')
		IntEq c1 t2				-> 	IntEq (fillWithContext c1 c') t2
		IntEq t1 c2				->	IntEq t1 (fillWithContext c2 c')
		IntLt c1 t2				->	IntLt (fillWithContext c1 c') t2
		IntLt t1 c2				->	IntLt t1 (fillWithContext c2 c')
		ParTerm c1				-> 	ParTerm (fillWithContext c1 c')
		Fix c1					->	Fix (fillWithContext c1 c')
		Let v1 c2 t3			->	Let v1 (fillWithContext c2 c') t3
		Let v1 t2 c3			->	Let v1 t2 (fillWithContext c3 c')
		
\end{code}


