\begin{code}
module CPS where
import qualified AbstractSyntax as S 
import qualified Typing as T

toCPS::S.Type -> S.Term -> S.Term
toCPS answerType t = case t of
  S.Var x        -> let k = if (x=="k") then "k`" else "k"
                       in S.Abs k (S.TypeArrow answerType answerType) 
                                  (S.App (Var k) t)
  S.Tru          -> S.Abs "k" (S.TypeArrow S.TypeBool answerType) 
                              (S.App (Var "k") t)
  S.Fls          -> S.Abs "k" (S.TypeArrow S.TypeBool answerType) 
                              (S.App (Var "k") t)
  S.IntConst x   -> S.Abs "k" (S.TypeArrow S.TypeInt answerType) 
                              (S.App (Var "k") t)
  S.Abs x tau t1 -> let k = checkFreeVars (S.fv t1) "k"
                       in S.Abs k (S.TypeArrow answerType answerType) 
                                  (S.App (Var k) (S.Abs x tau 
                                  	(toCPS (T.typeCheck t1) t1))
  S.App t1 t2    -> let k = checkFreeVars ((S.fv t1)++(S.fv t2)) "k"
                        v1= checkFreeVars ((S.fv t1)++(S.fv t2)) "v1"
                        v2= checkFreeVars ((S.fv t1)++(S.fv t2)) "v2"
                       in S.Abs k (S.TypeArrow answerType answerType)
                                  (S.App (toCPS (T.typeCheck t1) t1)
                                  	(S.Abs v1 
                                  		(S.TypeArrow answerType answerType) 
                                  		(S.App (toCPS (T.typeCheck t2) t2) 
                                  			(S.Abs v2 answerType 
                                  				(S.App (S.App v1 v2) k)))))

 | If Term Term Term |  IntAdd Term Term| IntSub Term Term
 | IntMul Term Term| IntDiv Term Term| IntNand Term Term| IntEq Term Term
 | IntLt Term Term | ParTerm Term| Fix Term| Let Var Term Term


checkFreeVars :: [Strings] -> String -> String
checkFreeVars fvs s = if (s `elem` fvs) then checkFreeVars fvs (s++"`") else s

\end{code}