\begin{code}
module CPS where
import qualified AbstractSyntax as S 
import qualified Typing as T

toCPS::S.Type -> S.Term -> S.Term
toCPS answerType t = case t of
  S.Var x        -> let k = if (x=="k") then "k`" else "k"
                       in S.Abs k answerType(S.App (S.Var k) t)
  S.Tru          -> S.Abs "k" answerType(S.App (S.Var "k") t)
  S.Fls          -> S.Abs "k" answerType(S.App (S.Var "k") t)
  S.IntConst x   -> S.Abs "k" answerType(S.App (S.Var "k") t)
  S.Abs x tau t1 -> let t1' =  toCPS answerType t1
                       in let k = checkFV (S.fv t1') "k"
                             in S.Abs k answerType (S.App (S.Var k) 
                                                    (S.Abs x tau t1'))
  --S.Let y (S.Fix t1) t2 -> 
  --  let aT = answerType
  --      x1 = checkFV (S.fv t1) "x1"
  --      in toCPS answerType (S.App 
  --                           (S.Abs y aT t2) 
  --                           (S.Abs x1 aT (S.App (S.Fix t1)(S.Var x1))))
  S.Let y (S.Fix (S.Abs f _ (S.Abs x _ t1))) t2 ->
    let aT = answerType
        t1'= toCPS aT t1
        t2'= toCPS aT t2
        k = checkFV (S.fv t1) "k"
        kf = checkFV (S.fv t1) "kf"
        v1 = checkFV (S.fv t1) "v1"
        in (S.Abs k aT
            (S.Let y 
             (S.Fix 
              (S.Abs f aT 
               (S.Abs x aT 
                (S.Abs kf aT
                 (S.App t1' 
                  (S.Abs v1 aT 
                   (S.App (S.Var kf)(S.Var v1) ))))))) 
             (S.App t2' (S.Var k)))) 
    --let aT = answerType
    --    t1'= toCPS aT t1
    --    t2'= toCPS aT (S.App (S.Var f) t2)
    --    k = checkFV (S.fv t1) "k"
    --    kf = checkFV (S.fv t1) "kf"
    --    v1 = checkFV (S.fv t1) "v1"
    --    in (S.Abs k aT
    --        (S.Let y 
    --         (S.Fix 
    --          (S.Abs f aT 
    --           (S.Abs x aT 
    --            (S.Abs kf aT
    --             (S.App t1' 
    --              (S.Abs v1 aT 
    --               (S.App (S.Var kf)(S.Var v1) ))))))) 
    --         (S.Abs f aT (S.App t2' (S.Var k)))))

  S.App (S.Fix (S.Abs f _ (S.Abs x _ t1))) t2 ->
    let aT = answerType
        t1'= toCPS aT t1
        t2'= toCPS aT (S.App (S.Var f) t2)
        k = checkFV (S.fv t1) "k"
        kf = checkFV (S.fv t1) "kf"
        v1 = checkFV (S.fv t1) "v1"
        in (S.Abs k aT 
            (S.App 
             (S.Abs f aT 
              (S.App t2' (S.Var k)))
             (S.Fix 
              (S.Abs f aT 
               (S.Abs x aT 
                (S.Abs kf aT 
                  (S.App t1' (S.Abs v1 aT (S.App (S.Var kf) (S.Var v1)))))) ))))      
  --S.Fix (S.Abs f _ (S.Abs x _ t1))  -> 
  --  let aT = answerType
  --      t1'= toCPS aT t1
  --      k = checkFV (S.fv t1) "k"
  --      v1 = checkFV (S.fv t1) "v1"
  --      v2 = checkFV (S.fv t1) "v2"
  --      in (S.Abs k aT
  --          (S.App (S.Abs f aT (S.Abs x  aT t1'))
  --           (S.Abs v1 aT 
  --            (S.App (S.Fix ((S.Abs f aT (S.Abs x  aT t1'))))  
  --             (S.Abs v2 aT 
  --              (S.App 
  --               (S.App (S.Var v1) (S.Var v2)) (S.Var k))))))) 
  --a (S.Fix (toCPS answerType t1)) of
  --                    f@(S.Fix (S.Abs k tau t1')) -> S.Abs k tau (S.App t1' f)
  S.App t1 t2    -> let t1' = toCPS answerType t1
                        t2' = toCPS answerType t2
                       in let k  = checkFV ((S.fv t1)++(S.fv t2)) "k"
                              v1 = checkFV ((S.fv t1)++(S.fv t2)) "v1"
                              v2 = checkFV ((S.fv t1)++(S.fv t2)) "v2"
                             in (S.Abs k answerType 
                                 (S.App t1'
                                  (S.Abs v1 answerType 
                                   (S.App t2'  
                                    (S.Abs v2 answerType 
                                     (S.App 
                                      (S.App (S.Var v1) (S.Var v2)) (S.Var k)))
                                       )))) 
  S.If t1 t2 t3  -> let k  = checkFV ((S.fv t1)++(S.fv t2)++(S.fv t3)) "k"
                        k1 = checkFV ((S.fv t1)++(S.fv t2)++(S.fv t3)) "k1"
                        v1 = checkFV ((S.fv t1)++(S.fv t2)++(S.fv t3)) "v1"
                        v2 = checkFV ((S.fv t1)++(S.fv t2)++(S.fv t3)) "v2"
                        v3 = checkFV ((S.fv t1)++(S.fv t2)++(S.fv t3)) "v3"
                        aT = answerType
                        t1'= toCPS aT t1
                        t2'= toCPS aT t2
                        t3'= toCPS aT t3
                        in S.Abs k aT
                            (S.App t1'
                             (S.Abs v1 aT
                              (S.App (S.If (S.Var v1) t2' t3') (S.Var k))))   
  S.Let x t1 t2   -> toCPS answerType (S.App (S.Abs x answerType t2) t1)
  S.ParTerm t1    -> toCPS answerType t1
  x               -> let k = checkFV (S.fv t) "k"
                         v1= checkFV (S.fv t) "v1"
                         v2= checkFV (S.fv t) "v2"
                         pairT = cpsPair answerType t
                        in S.Abs k answerType 
                                 (S.App (fst pairT) (S.Abs v1 S.TypeInt 
                                  (S.App (snd pairT) (S.Abs v2 S.TypeInt
                                    (S.App (S.Var k) (cpsOp x v1 v2))))))

cpsPair:: S.Type -> S.Term -> (S.Term, S.Term) 
cpsPair ty t = case t of
  (S.IntAdd t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntSub t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntMul t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntDiv t1 t2) -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntNand t1 t2)-> ((toCPS ty t1),(toCPS ty t2))
  (S.IntEq t1 t2)  -> ((toCPS ty t1),(toCPS ty t2))
  (S.IntLt t1 t2)  -> ((toCPS ty t1),(toCPS ty t2))
  _                -> error ("non-supported term sent to cpsPair")

cpsOp:: S.Term -> String -> String -> S.Term
cpsOp t v1 v2 = case t of
  S.IntAdd _ _ -> (S.IntAdd (S.Var v1)(S.Var v2))
  S.IntSub _ _ -> (S.IntSub (S.Var v1)(S.Var v2))
  S.IntMul _ _ -> (S.IntMul (S.Var v1)(S.Var v2))
  S.IntDiv _ _ -> (S.IntDiv (S.Var v1)(S.Var v2))
  S.IntNand _ _-> (S.IntNand (S.Var v1)(S.Var v2))
  S.IntEq _ _  -> (S.IntEq (S.Var v1)(S.Var v2))
  S.IntLt _ _  -> (S.IntLt (S.Var v1)(S.Var v2))
  _            -> error ("non-supported term sent to cpsOp")

checkFV :: [String] -> String -> String
checkFV fvs s = if (s `elem` fvs) then checkFV fvs (s++"`") else s

\end{code}