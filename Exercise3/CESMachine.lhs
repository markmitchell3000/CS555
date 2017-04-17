\begin{code}
module CESMachine where
import qualified DeBruijn as S
import qualified IntegerArithmetic as I

data Inst = Int Integer
          | Bool Bool
          | Op Op
          | Access Int
          | Close Code
          | Let
          | EndLet
          | Apply
          | Return
          | If
          | Fix
          deriving (Show, Eq)

data Op = Add
        | Sub
        | Mul
        | Div
        | Nand
        | Eq
        | Lt
        deriving (Show, Eq)
          
type Code = [Inst]
data Value = BoolVal Bool 
          | IntVal Integer 
          | Clo Code Env
          deriving (Show, Eq)
type Env = [Value]
data Slot = Value Value | Code Code | Env Env 
  deriving Show
type Stack = [Slot]
type State = (Code, Env, Stack)


compile::S.Term ->  Code
compile t = case t of
    --
    S.Var n             ->  [Access n]
    S.IntConst n        ->  [Int n]
    S.Tru               ->  [Bool True]
    S.Fls               ->  [Bool False]
    --
    S.IntAdd  t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Add]
    S.IntSub  t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Sub]
    S.IntMul  t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Mul]
    S.IntDiv  t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Div]
    S.IntNand t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Nand]
    S.IntEq   t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Eq]
    S.IntLt   t1 t2     ->  (compile t1) ++ (compile t2) ++ [Op Lt]
    --
    S.Abs     t1 t'     ->  [Close ((compile t') ++ [Return])]
    S.App     t1 t2     ->  (compile t1) ++ (compile t2) ++ [Apply]
    S.Let     t1 t2     ->  (compile t1) ++ [Let] ++ (compile t2) ++ [EndLet]
    S.Fix     t1        ->  (compile t1) ++ [Fix]
\end{code}
For the if case term t2 and t3 are placed inside of closures to postpone 
evaluation, this ensure we have a lazy if statement.
\begin{code}
    S.If      t1 t2 t3  ->  (compile t1) ++ [Close ((compile t2) ++ [Return])] 
                             ++ [Close ((compile t3) ++ [Return])] ++ [If]
    
step::State -> Maybe State
step state = case state of 
  ((Access n):c,e,s)  ->  case e !! n of
    (Clo t@(Close ((Close c1:c2)):[Fix]) []) -> Just (t++c, e, s)
    v -> Just(c,e, Value v:s)
  ((Int n):c,e,s)     ->  Just(c,e, (Value (IntVal n)):s)
  ((Bool b):c,e,s)    ->  Just(c,e, (Value (BoolVal b)):s)
  (If:c, e, (Value (Clo c3 e3)):(Value (Clo c2 e2)):(Value (BoolVal v)):s)  ->
    if v then Just (c2, e2, (Code c):(Env e):s)
         else Just (c3, e3, (Code c):(Env e):s)
  -- Ops
  ((Op o):c,e, (Value v2): (Value v1):s)      ->  Just(c,e, (opHelp o v1 v2):s)
  --
  (Return:c, e, v:(Code c'):(Env e'):s)       ->  Just (c', e', v:s)
  (Apply:c,e,(Value v) : (Value (Clo c' e')) : s) -> 
    Just(c',v:e', (Code c):(Env e):s)
  --
  (Let:c,e, Value v:s) -> Just(c,v:e,s)
  (EndLet:c,v:e,s)     -> Just(c,e,s)
  ((Close c1):c,e,s)   -> Just (c, e, (Value (Clo c1 e)):s)
  (Fix:c, e, (Value (Clo (Close c1:c2) e1)) : s)        ->
    let fClo = (Clo (Close ((Close c1:c2)):[Fix]) [])
       in Just (c, e, (Value (Clo (c1++c2) (fClo:(fixRemove e fClo)))) : s)
  otherwise            -> Nothing 

opHelp:: Op -> Value -> Value -> Slot
opHelp o (IntVal v1) (IntVal v2) = case o of
  Add -> Value (IntVal (I.intAdd v1 v2))
  Sub -> Value (IntVal (I.intSub v1 v2))
  Mul -> Value (IntVal (I.intMul v1 v2))
  Div -> Value (IntVal (I.intDiv v1 v2))
  Nand-> Value (IntVal (I.intNand v1 v2))
  Eq  -> Value (BoolVal (I.intEq v1 v2))
  Lt  -> Value (BoolVal (I.intLt v1 v2))

fixRemove:: Env->Value-> Env
fixRemove e fClo= let e' = reverse e
                 in take (fixRemoveHelper e' fClo 0) e'

fixRemoveHelper:: Env -> Value -> Int -> Int
fixRemoveHelper []  _  n = n
fixRemoveHelper (e:es) v n = if(e==v) then n else fixRemoveHelper es v (n+1)

loop:: State -> State
loop state = case step state of
    Just state'         ->  loop state'
    Nothing             ->  state

eval::S.Term -> Value
eval t = case loop (compile t, [],[]) of
    (_,_,Value v:_)     ->  v

\end{code}