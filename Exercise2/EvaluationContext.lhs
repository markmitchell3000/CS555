\begin{code}
module EvaluationContext where
import qualified AbstractSyntax as S
data Context  =  Hole
              |  AppT        Context S.Term
              |  AppV        S.Term Context -- where Term is a value
              |  If          Context S.Term S.Term
              ...

fillWithTerm :: Context -> S.Term -> S.Term
fillWithTerm c t = case c of
  Hole                  ->  t
  AppT c1 t2            ->  S.App (fillWithTerm c1 t) t2
  AppV t1 c2            ->  S.App t1 (fillWithTerm c2 t)
  If c1 t2 t3           ->  S.If (fillWithTerm c1 t) t2 t3
  ...

fillWithContext :: Context -> Context -> Context
fillWithContext c c' = case c of
  Hole                  ->  c'
  AppT c1 t2            ->  AppT (fillWithContext c1 c') t2
  AppV t1 c2            ->  AppV t1 (fillWithContext c2 c')
  If c1 t2 t3           ->  If (fillWithContext c1 c') t2 t3
  ...


\end{code}