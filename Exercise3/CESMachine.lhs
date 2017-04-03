\begin{code}
module CESMachine where

import qualified DeBruijn as S

data Inst = Int Integer
          | Bool Bool
          | Add
          | Sub
          | Mul
          | Div
          | Nand
          | Eq
          | Lt
          | Access Int
          | Close Code
          | Let
          | EndLet
          | Apply
          | Return
          | If
          | Fix
          deriving Show

type Code = [Inst]
data Value = BoolVal Bool | IntVal Integer | Clo Code Env
type Env = [Value]
data Slot = Value Value | Code Code | Env Env 
  deriving Show
type Stack = [Slot]
type State = (Code, Env, Stack)

compile::S.Term -> Code
compile t = case t of
  S.Var n -> [Access n]
  ...

step::State -> Maybe State
step state = case state of 
  (Access n:c,e,s) -> Just(c,e, Value (e!!n):s)
  ...

loop:: State -> State
loop state =
  case step state of
  	Just state' -> loop state'
  	Nothing     -> state

eval::S.Term -> Value
eval t = case loop (compile t, [],[]) of
  (_,_,Value v:_) -> v

\end{code}