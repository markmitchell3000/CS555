\begin{code}
module NaturalSemantics where
import Data.List
import qualified AbstractSyntax as S
import qualified IntegerArithmetic as I

eval :: S.Term -> S.Term
eval t = if (S.isValue t) then t
         else evalPattern t

evalPattern:: S.Term -> S.Term
evalPattern (S.ParTerm t)     = eval t
evalPattern (S.If t1 t2 t3)   = if ((eval t1)== S.Tru) then eval t2 else eval t3 
evalPattern (S.App t1 t2)     = appHelp (eval t1) t2
evalPattern (S.Fix t)         = fixHelp (eval t) (S.Fix t)
evalPattern (S.Let x t1 t2)   = eval (S.subst x (eval t1) t2)
evalPattern x                 = binaryOp x


binaryOp:: S.Term -> S.Term
binaryOp (S.IntAdd t1 t2)  = S.IntConst (I.intAdd (termToInt t1)(termToInt t2))
binaryOp (S.IntSub t1 t2)  = S.IntConst (I.intSub (termToInt t1)(termToInt t2))
binaryOp (S.IntMul t1 t2)  = S.IntConst (I.intMul (termToInt t1)(termToInt t2))
binaryOp (S.IntDiv t1 t2)  = S.IntConst (I.intDiv (termToInt t1)(termToInt t2))
binaryOp (S.IntNand t1 t2) = S.IntConst (I.intNand (termToInt t1)(termToInt t2))
binaryOp (S.IntEq t1 t2)   = 
  if (I.intEq (termToInt t1)(termToInt t2)) then S.Tru else S.Fls
binaryOp (S.IntLt t1 t2)   = 
  if (I.intLt (termToInt t1)(termToInt t2)) then S.Tru else S.Fls
binaryOp x                 = x
-- Type is not correct so it returns x since it is stuck

appHelp:: S.Term-> S.Term -> S.Term
appHelp (S.Abs x _ t1) t2 = eval (S.subst x (eval t2) t1)
apphelp x y = S.App x y
-- Type is not correct so it returns S.App x y since it is stuck

-- Just like apphelp but don't evalute the fix term inside right away
fixHelp:: S.Term-> S.Term -> S.Term
fixHelp (S.Abs x _ t1) t2 = eval (S.subst x t2 t1)
fixHelp _ x = x
-- Type is not correct so it returns x since it is stuck

termToInt:: S.Term -> Integer
termToInt (S.IntConst x) = x
termToInt x              = 
  let newX = eval x 
     in if x/= newX then termToInt (eval newX)
        else error ("Non integer in arithmetic application")
\end{code}