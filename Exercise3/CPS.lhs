\begin{code}
module CPS where
import qualified AbstractSyntax as S 
import qualified Typing as T

toCPS::S.Type -> S.Term -> S.Term
toCPS answerType t = case t of
  S.Var x        -> let k = if (x=="k") then "k`" else "k"
                       in S.Abs k (S.TypeArrow answerType answerType) 
                                  (S.App (S.Var k) t)
  S.Tru          -> S.Abs "k" (S.TypeArrow S.TypeBool answerType) 
                              (S.App (S.Var "k") t)
  S.Fls          -> S.Abs "k" (S.TypeArrow S.TypeBool answerType) 
                              (S.App (S.Var "k") t)
  S.IntConst x   -> S.Abs "k" (S.TypeArrow S.TypeInt answerType) 
                              (S.App (S.Var "k") t)
  S.Abs x tau t1 -> let k = checkFreeVars (S.fv t1) "k"
                       in S.Abs k (S.TypeArrow answerType answerType) 
                                  (S.App (S.Var k) (S.Abs x tau 
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
                                  				(S.App (S.App (S.Var v1) (S.Var v2)) 
                                            (S.Var k))))))
  S.If t1 t2 t3  -> let k = checkFreeVars ((S.fv t1)++(S.fv t2)) "k"
                        v1= checkFreeVars ((S.fv t1)++(S.fv t2)) "v1"
                        v2= checkFreeVars ((S.fv t1)++(S.fv t2)) "v2"
                        v3= checkFreeVars ((S.fv t1)++(S.fv t2)) "v3"
                        S.Abs k (S.TypeArrow answerType answerType)
                                  (S.App (toCPS (T.typeCheck t1) t1)
                                    (S.Abs v1 
                                      (S.TypeArrow answerType S.TypeBool) 
                                      (S.App (toCPS (T.typeCheck t2) t2) 
                                        (S.Abs v2 answerType 
                                          (S.App (toCPS (T.typeCheck t2) t2) 
                                            (S.Abs v2 answerType 
                                              (S.App (S.Var k)
                                                (S.If (S.Var v1) (S.Var v2) 
                                                  (S.Var v3)))))))))
  S.Fix t1        -> let k = checkFreeVars ((S.fv t1)++(S.fv t2)) "k"
                         v1= checkFreeVars ((S.fv t1)++(S.fv t2)) "v1"
                        in S.Abs k (S.TypeArrow answerType answerType)
                              (S.App (toCPS (T.typeCheck t1) t1) 
                                (S.Abs v1 (answerType) (S.Var k) 
                                  (S.Fix S.Var v1)))
  S.Let x t1 t2   -> toCPS answerType (S.App (S.Abs x (T.typeCheck t1) t2) t1)
  S.ParTerm t1    -> toCPS answerType t1
  x               -> let k = checkFreeVars ((S.fv t1)++(S.fv t2)) "k"
                         v1= checkFreeVars ((S.fv t1)++(S.fv t2)) "v1"
                         v2= checkFreeVars ((S.fv t1)++(S.fv t2)) "v2"
                         pairT = cpsPair answerType t
                         in let t' = case x of 
                            (S.IntAdd _ _) -> (S.IntAdd (S.Var v1)(S.Var v2))
                            (S.IntSub _ _) -> (S.IntSub (S.Var v1)(S.Var v2))
                            (S.IntMul _ _) -> (S.IntMul (S.Var v1)(S.Var v2))
                            (S.IntDiv _ _) -> (S.IntDiv (S.Var v1)(S.Var v2))
                            (S.IntNand _ _)-> (S.IntNand (S.Var v1)(S.Var v2))
                            (S.IntEq _ _)  -> (S.IntEq (S.Var v1)(S.Var v2))
                            (S.IntLt _ _)  -> (S.IntLt (S.Var v1)(S.Var v2))
                            in S.Abs k (S.TypeArrow answerType answerType)
                                 (S.App (fst pairT) (S.Abs v1 S.TypeInt 
                                  (S.App (snd pairT) (S.App (S.Var k) t')))

cpsPair:: S.Type -> S.Term -> S.Term 
cpsPair ty t = case t of
  (S.IntAdd t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntSub t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntMul t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntDiv t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntNand t1 t2)-> ((toCPS ty t1),(toCPS ty t2))
  (S.IntEq t1 t2)  -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntLt t1 t2)  -> ((toCPS ty t1),(toCPS ty t2))
  _                -> error ("non-supported term sent to cpsPair")


checkFreeVars :: [Strings] -> String -> String
checkFreeVars fvs s = if (s `elem` fvs) then checkFreeVars fvs (s++"`") else s

makeCPS :: S.Term -> S.Term
makeCPS t = toCPS (T.typeCheck t) t

\end{code}