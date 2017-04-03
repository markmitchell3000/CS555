\begin{code}
module CEKMachine where

import qualified AbstractSyntax as S
import qualified IntegerArithmetic as I

newtype Closure = Cls (S.Term, Environment)
                  deriving Show

newtype Environment = Env [(S.Var, Closure)]
                      deriving Show

emptyEnv :: Environment
emptyEnv = Env []

lookupEnv :: Environment -> S.Var -> Closure
lookupEnv (e@(Env [])) x  =  
  error ("variable " ++ x ++ " not bound in environment " ++ show e)
lookupEnv (Env ((v,c):t)) x
  | x == v     =  c
  | otherwise  =  lookupEnv (Env t) x

data Cont  =  MachineTerminate
           |  Fun                Closure Cont -- where Closure is a value
           |  Arg                Closure Cont
           |  If                 Closure Closure Cont -- lazy 
           |  Fix                Cont
           |  Let                S.Var Closure Cont
           |  Plus1              Closure Cont
           |  Plus2              Closure Cont 
           |  Minus1             Closure Cont
           |  Minus2             Closure Cont 
           |  Times1             Closure Cont
           |  Times2             Closure Cont 
           |  Div1               Closure Cont
           |  Div2               Closure Cont
           |  Nand1              Closure Cont
           |  Nand2              Closure Cont 
           |  Eq1                Closure Cont
           |  Eq2                Closure Cont 
           |  Lt1                Closure Cont
           |  Lt2                Closure Cont 

cekMachineStep :: (Closure, Cont) -> Maybe (Closure, Cont)
cekMachineStep (cl, k) = case cl of
  Cls(S.App t1 t2, e)          -> Just (Cls(t1, e), Arg (Cls(t2, e)) k)
  Cls(S.If t1 t2 t3, e)        -> Just (Cls(t1, e), 
                                        If (Cls(t2, e)) (Cls(t3, e)) k)
  Cls(S.Fix t1, e)             -> Just (Cls(t1, e), Fix k)
  Cls(S.Let x t1 t2, e)        -> Just (Cls(t1, e), Let x (Cls(t2, e)) k)
  Cls(S.IntAdd t1 t2, e)       -> Just (Cls(t1, e), Plus1 (Cls(t2, e)) k)
  Cls(S.IntSub t1 t2, e)       -> Just (Cls(t1, e), Minus1 (Cls(t2, e)) k)
  Cls(S.IntMul t1 t2, e)       -> Just (Cls(t1, e), Times1 (Cls(t2, e)) k)
  Cls(S.IntDiv t1 t2, e)       -> Just (Cls(t1, e), Div1 (Cls(t2, e)) k)
  Cls(S.IntNand t1 t2, e)      -> Just (Cls(t1, e), Nand1 (Cls(t2, e)) k)
  Cls(S.IntEq t1 t2, e)        -> Just (Cls(t1, e), Eq1 (Cls(t2, e)) k)
  Cls(S.IntLt t1 t2, e)        -> Just (Cls(t1, e), Lt1 (Cls(t2, e)) k)
  Cls(S.Var x, e)              -> Just (lookupEnv e x, k)
  Cls(t, e)                    -> if (S.isValue t) then cekHelper (cl, k)
                                  else Nothing

cekHelper:: (Closure, Cont) -> Maybe (Closure, Cont)
cekHelper (cl@(Cls(t,e)), k) = case k of
  MachineTerminate                  -> Nothing
  Fun (Cls((S.Abs x _ t12), (Env e'))) k' 
                                    -> Just(Cls(t12,Env((x, cl):e')), k')      
  Arg (Cls(t2,e')) k'               -> Just (Cls(t2,e'), Fun cl k')
  If (Cls(t2, e1)) (Cls(t3, e2)) k'      
    | t==S.Tru                      -> Just (Cls(t2, e1), k')
    | t==S.Fls                      -> Just (Cls(t3, e2), k')
    | otherwise                     -> Nothing 
  Fix k'                            -> fixHelper (Cls(S.Fix t, e), k')
  Let x (Cls(t2, (Env e'))) k'      -> Just (Cls(t2, Env((x, cl):e')), k')
  Plus1 (Cls(t2, e')) k'            -> Just (Cls(t2, e'), Plus2 cl k')
  Plus2 (Cls(v1,e')) k'             -> biOpHelp (Cls((S.IntAdd v1 t),e'), k') 
  Minus1 (Cls(t2, e')) k'           -> Just (Cls(t2, e'), Minus2 cl k')
  Minus2 (Cls(v1,e')) k'            -> biOpHelp (Cls((S.IntSub v1 t),e'), k') 
  Times1 (Cls(t2, e')) k'           -> Just (Cls(t2, e'), Times2 cl k')
  Times2 (Cls(v1,e')) k'            -> biOpHelp (Cls((S.IntMul v1 t),e'), k') 
  Div1 (Cls(t2, e')) k'             -> Just (Cls(t2, e'), Div2 cl k')
  Div2 (Cls(v1,e')) k'              -> biOpHelp (Cls((S.IntDiv v1 t),e'), k') 
  Nand1 (Cls(t2, e')) k'            -> Just (Cls(t2, e'), Nand2 cl k')
  Nand2 (Cls(v1,e')) k'             -> biOpHelp (Cls((S.IntNand v1 t),e'), k') 
  Eq1 (Cls(t2, e')) k'              -> Just (Cls(t2, e'), Eq2 cl k')
  Eq2 (Cls(v1,e')) k'               -> biOpHelp (Cls((S.IntEq v1 t),e'), k') 
  Lt1 (Cls(t2, e')) k'              -> Just (Cls(t2, e'), Lt2 cl k')
  Lt2 (Cls(v1,e')) k'               -> biOpHelp (Cls((S.IntLt v1 t),e'), k')
  otherwise                         -> Nothing 

fixHelper:: (Closure, Cont) -> Maybe(Closure, Cont)
fixHelper ( t@(Cls(S.Fix (S.Abs x y t1),(Env e))) ,k)= 
  Just(Cls(t1,Env((x, t):e)), k)
fixHelper ( _ , k)                           = Nothing  

biOpHelp::(Closure, Cont) -> Maybe(Closure, Cont)
biOpHelp (Cls (t, e), k) = case t of 
  S.IntAdd (S.IntConst t1) (S.IntConst t2) 
    -> Just (Cls(S.IntConst (I.intAdd t1 t2),e), k)
  S.IntSub (S.IntConst t1) (S.IntConst t2)
    -> Just (Cls(S.IntConst (I.intSub t1 t2),e), k)
  S.IntMul (S.IntConst t1) (S.IntConst t2) 
    -> Just (Cls(S.IntConst (I.intMul t1 t2),e), k)
  S.IntDiv (S.IntConst t1) (S.IntConst t2)
    -> Just (Cls(S.IntConst (I.intDiv t1 t2),e), k)
  S.IntNand (S.IntConst t1) (S.IntConst t2) 
    -> Just (Cls(S.IntConst (I.intNand t1 t2),e), k)
  S.IntEq (S.IntConst t1) (S.IntConst t2)
    -> Just ((if (I.intEq t1 t2) then Cls(S.Tru,e) else Cls(S.Fls,e)), k)
  S.IntLt (S.IntConst t1) (S.IntConst t2) 
    -> Just ((if (I.intLt t1 t2) then Cls(S.Tru,e) else Cls(S.Fls,e)), k)
  otherwise
    -> Nothing

cekMachineEvalHelp ::(Closure, Cont) -> (Closure, Cont)
cekMachineEvalHelp (cl, k) =
  case cekMachineStep (cl, k) of
    Just clk' -> cekMachineEvalHelp clk'
    Nothing -> (cl, MachineTerminate) 

cekMachineEval :: S.Term -> S.Term
cekMachineEval t = 
  let Cls (t', k)= fst(cekMachineEvalHelp (Cls(t, emptyEnv), MachineTerminate))
     in t'
\end{code}