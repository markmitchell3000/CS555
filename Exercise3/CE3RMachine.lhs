\begin{code}
module CE3RMachine where
import qualified DeBruijn as D 
import qualified IntegerArithmetic as I

data Inst = Int Integer Integer
          | Bool Integer Bool
          | Op Op
          | Access Integer Int
          | Close Integer Code
          | Apply1
          | Apply2
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
type Code = [Inst]
data Value = BoolVal Bool 
           | IntVal Integer 
           | Clo Code Env 
           | CloFix Code 
           | Empty 
           deriving (Show, Eq)
type Env = [Value]
type Registers =(Value,Value,Value)
type State = (Code, Env, Registers)

compile::D.Term ->  Code
compile t = case t of
  D.App k (D.If t1 t2 t3)   ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [If] ++(toCode 1 k)++ [Apply1]
  D.App (D.App t1 t2) t3    -> (toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Apply2]
  D.App t1 (D.IntAdd t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Add]
  D.App t1 (D.IntSub t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Sub]
  D.App t1 (D.IntMul t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Mul]
  D.App t1 (D.IntDiv t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Div]
  D.App t1 (D.IntNand t2 t3)->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Nand]
  D.App t1 (D.IntEq t2 t3)  ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Eq]  
  D.App t1 (D.IntLt t2 t3)  ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Op Lt]
  D.App t1 (D.Fix t2)       ->(toCode 1 t1) ++ (toCode 2 t2) ++[Fix]++ [Apply1]    
  D.App t1 t2               ->(toCode 1 t1) ++ (toCode 2 t2) ++ [Apply1]  
  otherwise                 ->(toCode 1 t)  

step::State -> Maybe State
step state = case state of 
\end{code}
The code for Int, Bool, Access and Close each simply put a value on one of three 
registers.
\begin{code}
  ((Int i x):c,e,regs)            -> Just (c,e,(getReg (IntVal x) i regs))
  ((Bool i x):c,e,regs)           -> Just (c,e,(getReg (BoolVal x) i regs))
  ((Access i x):c,e,regs)         -> Just (c,e,(getReg (e !! x) i regs))
  ((Close i x):c,e,regs)          -> Just (c,e,(getReg (Clo x e) i regs)
\end{code}
Apply1 - will do a single application so the value on register 2 is placed at the 
head of the environment, or index 0.

Apply2 - will do 2 applications so the inner most abstraction will return an 
abstraction which means that the value on register 2 will be for the free 
variable in the abstraction produced because of this we know that the debrujin 
value in this case will be 1 rather than 0. 
\begin{code}
  (Apply1:c,e,((Clo c1 e1),v2,v3))-> Just (c1,v2:e1,(Empty,Empty,Empty))
  (Apply2:c,e,((Clo c1 e1),v2,v3))-> Just (c1,v3:v2:e1,(Empty,Empty,Empty))

  (If:c,e,(BoolVal t1,t2,t3))     -> if t1 then Just (c,e,(Empty,t2,Empty))
                                     else Just (c,e,(Empty,t3,Empty))
  ((Op o):c,e,((Clo c1 e1),IntVal v2, IntVal v3))  -> 
    Just(c1,(OpHelp o v2 v3):e1, (Empty, Empty, Empty))
  otherwise                       -> Nothing

OpHelp:: Op -> Integer -> Integer -> Value
OpHelp o v1 v2 = case o of 
  Add -> IntVal (I.intAdd v2 v3)
  Sub -> IntVal (I.intSub v2 v3)
  Mul -> IntVal (I.intMul v2 v3) 
  Div -> IntVal (I.intDiv v2 v3) 
  Nand-> IntVal (I.intNand v2 v3)
  Eq  -> BoolVal (I.intEq v2 v3) 
  Lt  -> BoolVal (I.intLt v2 v3) 


getReg:: Value -> Int -> Registers -> Registers
getReg v' 1 (v1, v2, v3) = (v',v2,v3)
getReg v' 2 (v1, v2, v3) = (v1,v',v3)
getReg v' 3 (v1, v2, v3) = (v1,v2,v')

toCode:: Integer -> D.Term -> Code
toCode i t = case t of
    D.Var x              -> [Access i x]
    D.Tru                -> [Bool i True]
    D.Fls                -> [Bool i False]
    D.IntConst x         -> [Int i x]
    D.Abs _ (D.Abs _ t1) -> [Close i (compile t1)]
    D.Abs _ t1           -> [Close i (compile t1)]
    _                    -> error "incorrect term in toCode"

loop:: State -> State
loop state = case step state of
    Just state'         ->  loop state'
    Nothing             ->  state

eval::D.Term -> Value
eval t = case loop (compile t, [],(Empty,Empty,Empty)) of
    (_,_,(v,_,_))     ->  v              
\end{code}