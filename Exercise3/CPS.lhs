\begin{code}
module CPS where
import qualified AbstractSyntax as S 

toCPS::S.Type -> S.Term -> S.Term
toCPS answerType t = case t of
  S.Var x        -> let k = if (x=="k") then "k`" else "k"
                       in S.Abs k (S.TypeArrow S.TypeBool answerType) 
                                  (S.App (Var k) t)
  S.Tru          -> S.Abs "k" (S.TypeArrow S.TypeBool answerType) 
                              (S.App (Var "k") t)
  S.Fls          -> S.Abs "k" (S.TypeArrow S.TypeBool answerType) 
                              (S.App (Var "k") t)
  S.IntConst x   -> S.Abs "k" (S.TypeArrow S.TypeInt answerType) 
                              (S.App (Var "k") t)

   Abs Var Type Term | App Term Term |
 | If Term Term Term |  IntAdd Term Term| IntSub Term Term
 | IntMul Term Term| IntDiv Term Term| IntNand Term Term| IntEq Term Term
 | IntLt Term Term | ParTerm Term| Fix Term| Let Var Term Term


checkFreeVars :: [Strings] -> String -> String
checkFreeVars fvs s = if (s `elem` fvs) then checkFreeVars fvs (s++"`") else s

\end{code}