\begin{code}
module CEKMachine where

import Latex
import qualified AbstractSyntax as S

newtype Environment = Env [(S.Var, Closure)]
                      deriving Show
...
emptyEnv :: Environment
emptyEnv = Env []

lookupEnv :: Environment -> S.Var -> Closure
lookupEnv (e@(Env [])) x  =  error ("variable " ++ x ++ " not bound in environment " ++ show e)
lookupEnv (Env ((v,c):t)) x
  | x == v     =  c
  | otherwise  =  lookupEnv (Env t) x
...
data Cont  =  MachineTerminate
           |  Fun                Closure Cont -- where Closure is a value
           |  Arg                Closure Cont
           |  If                 Closure Closure Cont -- lazy 
           ...
cekMachineStep :: (Closure, Cont) -> Maybe (Closure, Cont)
...
cekMachineEval :: S.Term -> S.Term
...
\end{code}