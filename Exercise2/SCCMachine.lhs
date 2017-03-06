\begin{code}
module SCCMachine where

import Latex
import qualified AbstractSyntax as S
import qualified EvaluationContext as E

sccMachineStep :: (S.Term, E.Context) -> Maybe (S.Term, E.Context)
...
sccMachineEval :: S.Term -> S.Term
...
\end{code}