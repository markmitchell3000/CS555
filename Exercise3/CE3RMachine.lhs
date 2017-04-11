\begin{code}
module CE3RMachine where
import qualified CPS as C
import qualified DeBruijn as D 
import qualified IntegerArithmetic as I

data Inst = Int Integer Integer
          | Bool Integer Bool
          | Add
          | Sub
          | Mul
          | Div
          | Nand
          | Eq
          | Lt
          | Access Integer Int
          | Close Integer Code
          | Let
          | EndLet
          | Apply1
          | Apply2
          | Return
          | If
          | Fix
          deriving (Show, Eq)
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

toCode:: Integer -> D.Term -> Code
toCode i t = case t of
    D.Var x              -> [Access i x]
    D.Tru                -> [Bool i True]
    D.Fls                -> [Bool i False]
    D.IntConst x         -> [Int i x]
    D.Abs _ (D.Abs _ t1) -> [Close i (compile t1)]
    D.Abs _ t1           -> [Close i (compile t1)]
    _                    -> error "incorrect term in toCode"

compile::D.Term ->  Code
compile t = case t of
  D.App k (D.If t1 t2 t3)   ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [If] ++(toCode 1 k)++ [Apply1]
  D.App (D.App t1 t2) t3    -> (toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Apply2]
  D.App t1 (D.IntAdd t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Add]
  D.App t1 (D.IntSub t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Sub]
  D.App t1 (D.IntMul t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Mul]
  D.App t1 (D.IntDiv t2 t3) ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Div]
  D.App t1 (D.IntNand t2 t3)->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Nand]
  D.App t1 (D.IntEq t2 t3)  ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Eq]  
  D.App t1 (D.IntLt t2 t3)  ->(toCode 1 t1) ++ (toCode 2 t2) ++ (toCode 3 t3) 
                              ++ [Lt]
  D.App t1 (D.Fix t2)       ->(toCode 1 t1) ++ (toCode 2 t2) ++ [Apply1]    
  D.App t1 t2               ->(toCode 1 t1) ++ (toCode 2 t2) ++ [Apply1]  
  otherwise                 ->(toCode 1 t)  

step::State -> Maybe State
step state = case state of 
  ((Int 1 x):c,e,(v1,v2,v3))      -> Just (c,e,(IntVal x, v2, v3))
  ((Int 2 x):c,e,(v1,v2,v3))      -> Just (c,e,(v1, IntVal x, v3))
  ((Int 3 x):c,e,(v1,v2,v3))      -> Just (c,e,(v1, v2, IntVal x))
  ((Bool 1 x):c,e,(v1,v2,v3))     -> Just (c,e,(BoolVal x, v2, v3))
  ((Bool 2 x):c,e,(v1,v2,v3))     -> Just (c,e,(v1, BoolVal x, v3))
  ((Bool 3 x):c,e,(v1,v2,v3))     -> Just (c,e,(v1, v2, BoolVal x))
  ((Access 1 x):c,e,(v1,v2,v3))   -> Just (c,e,(e !! x, v2, v3))
  ((Access 2 x):c,e,(v1,v2,v3))   -> Just (c,e,(v1, e !! x, v3))
  ((Access 3 x):c,e,(v1,v2,v3))   -> Just (c,e,(v1, v2, e !! x))
  ((Close 1 x):c,e,(v1,v2,v3))    -> Just (c,e,((Clo x e), v2, v3))
  ((Close 2 x):c,e,(v1,v2,v3))    -> Just (c,e,(v1, (Clo x e), v3))
  ((Close 3 x):c,e,(v1,v2,v3))    -> Just (c,e,(v1, v2, (Clo x e)))
  (Apply1:c,e,((Clo c1 e1),v2,v3))-> Just (c1,v2:e1,(Empty,Empty,Empty))
  (Apply2:c,e,((Clo c1 e1),v2,v3))-> Just (c1,v3:v2:e1,(Empty,Empty,Empty))
  (If:c,e,(BoolVal v1,t2,t3))     -> if v1 then Just (c,e,(Empty,t2,Empty))
                                     else Just (c,e,(Empty,t3,Empty))
  (Add:c,e,((Clo c1 e1),IntVal v2, IntVal v3))  -> 
    Just(c1,(IntVal (I.intAdd v2 v3)):e1, (Empty, Empty, Empty)) 
  (Sub:c,e,((Clo c1 e1),IntVal v2, IntVal v3))  -> 
    Just(c1,(IntVal (I.intSub v2 v3)):e1, (Empty, Empty, Empty))
  (Mul:c,e,((Clo c1 e1),IntVal v2, IntVal v3))  -> 
    Just(c1,(IntVal (I.intMul v2 v3)):e1, (Empty, Empty, Empty)) 
  (Div:c,e,((Clo c1 e1),IntVal v2, IntVal v3))  -> 
    Just(c1,(IntVal (I.intDiv v2 v3)):e1, (Empty, Empty, Empty)) 
  (Nand:c,e,((Clo c1 e1),IntVal v2, IntVal v3)) -> 
    Just(c1,(IntVal (I.intNand v2 v3)):e1, (Empty, Empty, Empty))
  (Eq:c,e,((Clo c1 e1),IntVal v2, IntVal v3))   -> 
    Just(c1,(BoolVal (I.intEq v2 v3)):e1, (Empty, Empty, Empty)) 
  (Lt:c,e,((Clo c1 e1),IntVal v2, IntVal v3))   -> 
    Just(c1,(BoolVal (I.intLt v2 v3)):e1, (Empty, Empty, Empty)) 
  otherwise                       -> Nothing

loop:: State -> State
loop state = case step state of
    Just state'         ->  loop state'
    Nothing             ->  state

eval::D.Term -> Value
eval t = case loop (compile t, [],(Empty,Empty,Empty)) of
    (_,_,(v,_,_))     ->  v              
\end{code}