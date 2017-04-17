\begin{code}
module NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices where

import Data.Maybe
import qualified DeBruijn as S
import qualified IntegerArithmetic as I

data Value = BoolVal Bool| IntVal Integer| Clo S.Term Env 
  deriving Show

type Env = [Value]

\end{code}
This is very similar to the previous Natural semantics but our values now 
uses closures in place of abstractions.  This allows us to carry variable values
in our enviroment rather than calling a substitution function.  Since this uses
DeBruijn terms rather then variable names we can use these as indexs of the 
environment to locate the values of our variables.  
\begin{code}

evalInEnv::Env -> S.Term -> Maybe Value
evalInEnv e t = case t of
  S.Tru             -> Just(BoolVal True)
  S.Fls             -> Just(BoolVal False)
  S.IntConst x      -> Just (IntVal x)
  S.ParTerm t1      -> evalInEnv e t1
  S.If t1 t2 t3     -> case (evalInEnv e t1) of
                           Just(BoolVal True) -> evalInEnv e t2
                           Just(BoolVal False)-> evalInEnv e t3
                           otherwise          -> Just(Clo t e)
  S.Var i           -> if((length e)>i) 
                       then case (e!!i) of
                         (Clo t' e') -> evalInEnv e' t'
                         x           -> Just x
                       else Just(Clo t e)
  S.Abs ty t1       -> Just(Clo t e)
  S.App t1 t2       -> case (evalInEnv e t1) of
                           Just (Clo a@(S.Abs _ t1') e') -> 
                             case (evalInEnv e t2) of
                               Just t2' -> evalInEnv (t2':e') t1' 
                               otherwise-> Just (Clo (S.App a t2) e)
                           otherwise-> Just(Clo t e)
\end{code}
Fix t will be put inside a closure and added to the environment the term inside 
the abstraction t.  The term t itself should be looking for the fix function and 
then whatever values it requires.  For this reason we need to look inside the 
abstraction to evaluate the term, and then if it requires a recusive call it may 
call the closure with fix t.
\begin{code}                           
  S.Fix t1          -> case (evalInEnv e t1) of
                           Just (Clo (S.Abs _ t1') e') 
                             -> evalInEnv ((Clo t e'):e) t1'
                           otherwise -> Just(Clo t e)
  S.Let t1 t2       -> case (evalInEnv e t1) of
                           Just t1' -> evalInEnv (t1':e) t2 
                           otherwise-> Just (Clo t e)
  x                 -> case (binaryOp e x) of
                           Just x' -> Just x'
                           Nothing -> Just(Clo t e)

binaryOp:: Env -> S.Term -> Maybe Value
binaryOp e (S.IntAdd t1 t2)  = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> Just (IntVal (I.intAdd x y))
        otherwise      -> Nothing
    otherwise-> Nothing 
binaryOp e (S.IntSub t1 t2)  = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> Just (IntVal (I.intSub x y))
        otherwise      -> Nothing
    otherwise-> Nothing         
binaryOp e (S.IntMul t1 t2)  = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> Just (IntVal (I.intMul x y))
        otherwise      -> Nothing
    otherwise-> Nothing    
binaryOp e (S.IntDiv t1 t2)  = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> Just (IntVal (I.intDiv x y))
        otherwise      -> Nothing
    otherwise-> Nothing    
binaryOp e (S.IntNand t1 t2) = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> Just (IntVal (I.intNand x y))
        otherwise      -> Nothing
    otherwise-> Nothing    
binaryOp e (S.IntEq t1 t2)   = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> if (I.intEq x y) then Just(BoolVal True) 
                    else Just(BoolVal False)
        otherwise      -> Nothing
    otherwise-> Nothing          
binaryOp e (S.IntLt t1 t2)   = 
  case (evalInEnv e t1) of
    Just(IntVal x) -> case (evalInEnv e t2) of
        Just(IntVal y) -> if (I.intLt x y) then Just(BoolVal True) 
                    else Just(BoolVal False)
        otherwise      -> Nothing
    otherwise-> Nothing 
binaryOp e x                 = Nothing

eval:: S.Term -> Value
eval t = fromJust (evalInEnv [] t)

\end{code}