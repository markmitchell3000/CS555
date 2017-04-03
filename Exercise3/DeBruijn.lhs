\begin{code}
module DeBruijn where
import Data.List
import qualified AbstractSyntax as S

type Type = S.Type
data Term =  Var Int
           | Abs Type Term
           | App Term Term
           | If Term Term Term
           | Fix Term
           | Let Term Term
           | IntAdd Term Term
           | IntSub Term Term
           | IntMul Term Term
           | IntDiv Term Term
           | IntNand Term Term
           | IntEq Term Term
           | IntLt Term Term 
           | ParTerm Term
           | Tru 
           | Fls
           | IntConst Integer

instance Show Term where
  show (Var x)       = "~"++(show x)
  show (Abs y z)     = "abs("++(show y)++"."++(show z)++")"
  show (App x y)     = "app("++(show x)++","++(show y)++")"
  show Tru           = "true"
  show Fls           = "false"
  show (If x y z)    = "if "++(show x)++" then "++(show y)++" else " ++(show z)
                      ++" fi"
  show (Fix x)       = "fix "++(show x)
  show (Let y z)     = "let "++ (show y)++" in " ++(show z)++ " end"
  show (IntConst x)  = show x
  show (IntAdd x y)  = "+(" ++ (show x) ++","++ (show y) ++")"
  show (IntSub x y)  = "-(" ++ (show x) ++","++ (show y) ++")"
  show (IntMul x y)  = "*(" ++ (show x) ++","++ (show y) ++")"
  show (IntDiv x y)  = "/(" ++ (show x) ++","++ (show y) ++")"
  show (IntNand x y) = "^(" ++ (show x) ++","++ (show y) ++")"
  show (IntEq x y)   = "=(" ++ (show x) ++","++ (show y) ++")"
  show (IntLt x y)   = "<(" ++ (show x) ++","++ (show y) ++")"
  show (ParTerm x)   = "("++(show x) ++")"

deBruijnStep:: S.Term -> [String] -> Maybe Term
deBruijnStep t xs = case t of
  S.Var x             -> case (elemIndex x xs) of
                             Just i    -> Just(Var i)
                             otherwise -> Nothing
  S.Abs x ty1 t1      -> case (deBruijnStep t1 (x:xs)) of
                             Just t1'  -> Just (Abs ty1 t1')
                             otherwise -> Nothing
  S.App t1 t2         -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (App t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.If t1 t2 t3       -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> case (deBruijnStep t3 xs) of
                                    Just t3' -> Just(If t1' t2' t3')
                                    otherwise -> Nothing
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.Fix t1            -> case (deBruijnStep t1 xs) of
                             Just t1'  -> Just (Fix t1')
                             otherwise -> Nothing
  S.Let x t1 t2       -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 (x:xs)) of
                                Just t2'  -> Just (Let t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntAdd t1 t2      -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntAdd t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntSub t1 t2      -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntSub t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntMul t1 t2      -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntMul t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntDiv t1 t2      -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntDiv t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntNand t1 t2     -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntNand t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntEq t1 t2       -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntEq t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.IntLt t1 t2       -> case (deBruijnStep t1 xs) of
                             Just t1' -> case (deBruijnStep t2 xs) of
                                Just t2'  -> Just (IntLt t1' t2')
                                otherwise -> Nothing
                             otherwise -> Nothing
  S.ParTerm t1        -> case (deBruijnStep t1 xs) of
                             Just t1' -> Just (ParTerm t1')
                             otherwise-> Nothing
  S.IntConst i        -> Just (IntConst i)
  S.Tru               -> Just Tru 
  S.Fls               -> Just Fls

toDeBruijn:: S.Term -> Term
toDeBruijn t = case (deBruijnStep t []) of 
                   Just t' -> t'
                   otherwise -> error ("Unable to convert to DeBruijin form!")

\end{code}