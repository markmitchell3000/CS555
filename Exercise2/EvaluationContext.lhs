\begin{code}
module EvaluationContext where
import qualified AbstractSyntax as S
data Context  =  Hole
    |  AppT         Context S.Term
    |  AppV         S.Term Context 
    |  If           Context S.Term S.Term
    |  IntAddT    Context S.Term
    |  IntAddV    S.Term Context
    |  IntSubT    Context S.Term
    |  IntSubV    S.Term Context
    |  IntMulT    Context S.Term
    |  IntMulV    S.Term Context
    |  IntDivT    Context S.Term
    |  IntDivV    S.Term Context
    |  IntNandT   Context S.Term
    |  IntNandV   S.Term Context
    |  IntEqT   Context S.Term
    |  IntEqV     S.Term Context
    |  IntLtT     Context S.Term 
    |  IntLtV     S.Term Context
    |  ParTerm    Context
    |  Fix      Context
    |  LetT     S.Var Context S.Term
    |  LetV     S.Var S.Term Context

fillWithTerm :: Context -> S.Term -> S.Term
fillWithTerm c t = case c of
    Hole                  ->  t
    AppT c1 t2              ->  S.App (fillWithTerm c1 t) t2
    AppV t1 c2              ->  S.App t1 (fillWithTerm c2 t)
    If c1 t2 t3             ->  S.If (fillWithTerm c1 t) t2 t3
    IntAddT c1 t2     ->  S.IntAdd (fillWithTerm c1 t) t2
    IntAddV t1 c2     ->  S.IntAdd t1 (fillWithTerm c2 t)
    IntSubT c1 t2     ->  S.IntSub (fillWithTerm c1 t) t2
    IntSubV t1 c2     ->  S.IntSub t1 (fillWithTerm c2 t)
    IntMulT c1 t2     ->  S.IntMul (fillWithTerm c1 t) t2
    IntMulV t1 c2     ->  S.IntMul t1 (fillWithTerm c2 t)
    IntDivT c1 t2     ->  S.IntDiv (fillWithTerm c1 t) t2
    IntDivV t1 c2     ->  S.IntDiv t1 (fillWithTerm c2 t)
    IntNandT c1 t2      ->  S.IntNand (fillWithTerm c1 t) t2
    IntNandV t1 c2      ->  S.IntNand t1 (fillWithTerm c2 t)
    IntEqT c1 t2      ->  S.IntEq (fillWithTerm c1 t) t2
    IntEqV t1 c2      ->  S.IntEq t1 (fillWithTerm c2 t)
    IntLtT c1 t2      ->  S.IntLt (fillWithTerm c1 t) t2
    IntLtV t1 c2      ->  S.IntLt t1 (fillWithTerm c2 t)
    ParTerm c1        ->  S.ParTerm (fillWithTerm c1 t)
    Fix c1          ->  S.Fix (fillWithTerm c1 t)
    LetT v1 c2 t3     ->  S.Let v1 (fillWithTerm c2 t) t3
    LetV v1 t2 c3     ->  S.Let v1 t2 (fillWithTerm c3 t)

fillWithContext :: Context -> Context -> Context
fillWithContext c c' = case c of
    Hole              ->  c'
    AppT c1 t2        ->  AppT (fillWithContext c1 c') t2
    AppV t1 c2        ->  AppV t1 (fillWithContext c2 c')
    If c1 t2 t3       ->  If (fillWithContext c1 c') t2 t3
    IntAddT c1 t2     ->  IntAddT (fillWithContext c1 c') t2
    IntAddV t1 c2     ->  IntAddV t1 (fillWithContext c2 c')
    IntSubT c1 t2     ->  IntSubT (fillWithContext c1 c') t2
    IntSubV t1 c2     ->  IntSubV t1 (fillWithContext c2 c')
    IntMulT c1 t2     ->  IntMulT (fillWithContext c1 c') t2
    IntMulV t1 c2     ->  IntMulV t1 (fillWithContext c2 c')
    IntDivT c1 t2     ->  IntDivT (fillWithContext c1 c') t2
    IntDivV t1 c2     ->  IntDivV t1 (fillWithContext c2 c')
    IntNandT c1 t2    ->  IntNandT (fillWithContext c1 c') t2
    IntNandV t1 c2    ->  IntNandV t1 (fillWithContext c2 c')
    IntEqT c1 t2      ->  IntEqT (fillWithContext c1 c') t2
    IntEqV t1 c2      ->  IntEqV t1 (fillWithContext c2 c')
    IntLtT c1 t2      ->  IntLtT (fillWithContext c1 c') t2
    IntLtV t1 c2      ->  IntLtV t1 (fillWithContext c2 c')
    ParTerm c1        ->  ParTerm (fillWithContext c1 c')
    Fix c1            ->  Fix (fillWithContext c1 c')
    LetT v1 c2 t3     ->  LetT v1 (fillWithContext c2 c') t3
    LetV v1 t2 c3     ->  LetV v1 t2 (fillWithContext c3 c')
    
\end{code}


