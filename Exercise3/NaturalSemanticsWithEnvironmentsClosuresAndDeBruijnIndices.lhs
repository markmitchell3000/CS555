\begin{code}
module NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices where

import Data.Maybe
import qualified DeBruijn as S

data Value = BoolVal Bool| IntVal Integer| Clo S.Term Env 
  deriving Show

type Env = [Value]

evalInEnv::Env -> S.Term -> Maybe Value
...

eval:: S.Term -> Value
eval t = fromJust (evalInEnv [] t)

\end{code}