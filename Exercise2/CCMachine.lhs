\begin{code}
module CCMachine where

import qualified AbstractSyntax as S
import qualified EvaluationContext as E

ccMachineStep :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
ccMachineStep (t, c) = case t of
  S.App t1 t2
    | not (S.isValue t1)                      ->   Just (t1, E.fillWithContext c (E.AppT E.Hole t2))       {-cc1-}
    | S.isValue t1 && not (S.isValue t2)      ->   Just (t2, E.fillWithContext c (E.AppV t1 E.Hole))       {-cc2-}
  S.App (S.Abs x _ t12) t2                    ->   Just (S.subst x t2 t12, c)                              {-ccbeta-}
  ...
ccMachineEval :: S.Term -> S.Term
...
\end{code}