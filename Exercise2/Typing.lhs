\begin{code}
module Typing where

import Data.Maybe
import Data.List
import qualified AbstractSyntax as S

data Context  =  Empty
              |  Bind Context S.Var S.Type
              deriving Eq

instance Show Context where
  show Empty                  =  "<>"
  show (Bind capGamma x tau)  =  show capGamma ++ "," ++ x ++ ":" ++ show tau

contextLookup :: S.Var -> Context -> Maybe S.Type
contextLookup x Empty  =  Nothing
contextLookup x (Bind capGamma y tau)
  | x == y      =  Just tau
  | otherwise   =  contextLookup x capGamma

typing :: Context -> S.Term -> Maybe S.Type
typing capGamma t = case t of
  S.Var x -> contextLookup x capGamma
  S.Abs x tau1 t2 -> do tau2 <- typing (Bind capGamma x tau1) t2; Just (S.TypeArrow tau1 tau2)
  S.App t1 t2 -> do S.TypeArrow tau11 tau12 <- typing capGamma t1
                    tau <- typing capGamma t2
                    if tau == tau11 then Just tau12 else Nothing
  S.Tru -> Just S.TypeBool
  S.Fls -> Just S.TypeBool
  S.If t1 t2 t3 -> do S.TypeBool <- typing capGamma t1
                      tau <- typing capGamma t2
                      tau' <- typing capGamma t3
                      if tau' == tau then Just tau else Nothing
  S.Let x t1 t2 -> do tau1 <- typing capGamma t1
                      typing (Bind capGamma x tau1) t2
  S.Fix t -> do (S.TypeArrow tau1 tau2) <- typing capGamma t
                             Just tau2
  S.IntConst _ -> Just S.TypeInt
  S.IntAdd t1 t2 -> arith t1 t2
  S.IntSub t1 t2 -> arith t1 t2
  S.IntMul t1 t2 -> arith t1 t2
  S.IntDiv t1 t2 -> arith t1 t2
  S.IntNand t1 t2 -> arith t1 t2
  S.IntEq t1 t2 -> rel t1 t2
  S.IntLt t1 t2 -> rel t1 t2
  where
    arith t1 t2 = do S.TypeInt <- typing capGamma t1; S.TypeInt <- typing capGamma t2; Just S.TypeInt
    rel t1 t2 = do S.TypeInt <- typing capGamma t1; S.TypeInt <- typing capGamma t2; Just S.TypeBool

typeCheck :: S.Term -> S.Type
typeCheck t =
  case typing Empty t of
    Just tau -> tau
    _ -> error "type error"
\end{code}