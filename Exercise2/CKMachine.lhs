\begin{code}
module CKMachine where

import qualified AbstractSyntax as S

data Cont  =  MachineTerminate
           |  Fun              S.Term Cont -- where Term is a value
           |  Arg              S.Term Cont
           |  If               S.Term S.Term Cont
           ...
ckMachineStep :: (S.Term, Cont) -> Maybe (S.Term, Cont)
...
ckMachineEval :: S.Term -> S.Term
...
\end{code}