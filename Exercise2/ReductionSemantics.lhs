\begin{code}
module ReductionSemantics where
import qualified AbstractSyntax as S
import qualified EvaluationContext as E
makeEvalContext :: S.Term -> Maybe (S.Term, E.Context)
makeEvalContext t = case t of
  S.App (S.Abs x tau11 t12) t2
    |  S.isValue t2 -> Just (t, E.Hole)
  S.App t1 t2
    |  S.isValue t1 -> ...
    |  otherwise -> ...
  S.If (S.Const S.Tru) t2 t3 -> Just (t, E.Hole)
  ...
  _ -> Nothing

makeContractum :: S.Term -> S.Term
makeContractum t = case t of
  S.App (S.Abs x tau11 t12) t2               ->  S.subst x t2 t12
  ...

textualMachineStep :: S.Term -> Maybe S.Term
textualMachineStep t = ... (E.fillWithTerm c (makeContractum t1)) ...

textualMachineEval :: S.Term -> S.Term
textualMachineEval t =
  case textualMachineStep t of
    Just t' -> textualMachineEval t'
    Nothing -> t
\end{code}