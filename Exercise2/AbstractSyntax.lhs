\begin{code}
module AbstractSyntax where

import System.Environment
import Data.Char

data Token =  TkArr| TkLPar| TkComma| TkRPar| TkBool| TkIntWrd| TkVarId String
 | TkAbs| TkColon| TkFullStop| TkApp|  TkTrue| TkFalse| TkIf| TkThen | TkElse
 | TkFi| TkIntLit Integer| TkPlus| TkMinus| TkMul| TkDiv| TkNand| TkEq| TkLt 
 | TkFix| TkLet| TkIn| TkEnd
 deriving (Show, Eq)

data Type = TypeArrow Type Type | TypeBool  | TypeInt deriving (Eq)

type Var = String

data Term = Var Var | Abs Var Type Term | App Term Term | Tru | Fls 
 | If Term Term Term | IntConst Integer| IntAdd Term Term| IntSub Term Term
 | IntMul Term Term| IntDiv Term Term| IntNand Term Term| IntEq Term Term
 | IntLt Term Term | ParTerm Term| Fix Term| Let Var Term Term
 deriving (Eq)

instance Show Type where
  show (TypeArrow x y)= "->("++(show x)++","++(show y)++")"
  show TypeBool  = "Bool"
  show TypeInt   = "Int"

instance Show Term where
  show (Var x)       = x
  show (Abs x y z)   = "abs("++x++":"++(show y)++"."++(show z)++")"
  show (App x y)     = "app("++(show x)++","++(show y)++")"
  show Tru           = "true"
  show Fls           = "false"
  show (If x y z)    = "if "++(show x)++" then "++(show y)++" else " ++(show z)
                      ++" fi"
  show (IntConst x)  = show x
  show (IntAdd x y)  = "+(" ++ (show x) ++","++ (show y) ++")"
  show (IntSub x y)  = "-(" ++ (show x) ++","++ (show y) ++")"
  show (IntMul x y)  = "*(" ++ (show x) ++","++ (show y) ++")"
  show (IntDiv x y)  = "/(" ++ (show x) ++","++ (show y) ++")"
  show (IntNand x y) = "^(" ++ (show x) ++","++ (show y) ++")"
  show (IntEq x y)   = "=(" ++ (show x) ++","++ (show y) ++")"
  show (IntLt x y)   = "<(" ++ (show x) ++","++ (show y) ++")"
  show (ParTerm x)   = "("++(show x) ++")"

commaSeperated:: [Token]
commaSeperated=[TkArr,TkApp,TkPlus, TkMinus, TkMul, TkDiv, TkNand, TkEq, TkLt]

-- Take a string and converts it to tokens
makeTokens :: [Char] -> [Token]
makeTokens cs = makeTokenList [] cs

-- Builds token list, ignores spaces
makeTokenList :: [Token] -> [Char] -> [Token]
makeTokenList ls [] = reverse ls
makeTokenList ls (x:xs) | (x=='-')&&((head xs) =='>') 
                          = makeTokenList (TkArr:ls) (tail xs)
                        | x == '(' = makeTokenList (TkLPar:ls) xs
                        | x == ',' = makeTokenList (TkComma:ls) xs
                        | x == ')' = makeTokenList (TkRPar:ls) xs
                        | x == ':' = makeTokenList (TkColon:ls) xs
                        | x == '.' = makeTokenList (TkFullStop:ls) xs
                        | x == '+' = makeTokenList (TkPlus:ls) xs
                        | x == '-' = makeTokenList (TkMinus:ls) xs
                        | x == '*' = makeTokenList (TkMul:ls) xs
                        | x == '/' = makeTokenList (TkDiv:ls) xs                        
                        | x == '^' = makeTokenList (TkNand:ls) xs
                        | x == '=' = makeTokenList (TkEq:ls) xs
                        | x == '<' = makeTokenList (TkLt:ls) xs                         
                        | isSpace x = makeTokenList ls xs
                        | isAlphaNum x= let alphas= takeWhile isAlphaNum (x:xs)
                                            rest = dropWhile isAlphaNum (x:xs)
                                      in  makeTokenList 
                                      ((matchToken alphas):ls) rest
                        | otherwise = error ("unrecognized character " 
                          ++ show x)  

-- Multiple char cases such as key words are handled by this function
matchToken :: [Char] -> Token
matchToken "Bool"   = TkBool
matchToken "Int"    = TkIntWrd
matchToken "abs"    = TkAbs
matchToken "app"    = TkApp
matchToken "true"   = TkTrue
matchToken "false"  = TkFalse
matchToken "if"     = TkIf
matchToken "then"   = TkThen
matchToken "else"   = TkElse
matchToken "fi"     = TkFi
matchToken x        = if (isInt x) then TkIntLit (read x::Integer) else TkVarId x

isInt :: [Char] -> Bool
isInt xs = foldr (\x y -> (elem x ['0'..'9']) && y ) True xs

-- returns type from tokens
tokenType:: [Token] -> Type
tokenType [TkIntWrd] = TypeInt
tokenType [TkBool]   = TypeBool
tokenType [TkArr]    = error ("Improper Token used for type")
tokenType (TkArr:xs) = if ((head xs)==TkLPar) then typeArrHelp (xs) 
                          else error ("Improper Token used for type")
tokenType xs         = error ("Improper Token used for type")

-- Gets the String that is designated as the variable
getVar :: Token -> Var
getVar (TkVarId x) = x
getVar x = error ("Improper variable "++show x)

-- Creates an arrow type from a list of tokens
typeArrHelp:: [Token] -> Type
typeArrHelp xs = 
  let arrTypes = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
     in TypeArrow (tokenType (fst arrTypes)) (tokenType (snd arrTypes))

-- Takes tokens that return terminal terms that do not contain other terms
makeSingleTerm :: Token -> Term
makeSingleTerm TkTrue = Tru
makeSingleTerm TkFalse = Fls
makeSingleTerm (TkVarId x) = Var x
makeSingleTerm (TkIntLit x) = IntConst x
makeSingleTerm x = error ("Undefined Term for token " ++ show x)

-- Takes a list of tokens to return a single term
buildTerm ::[Token] -> Term 
buildTerm [] = error ("No tokens provided")
buildTerm [x] = makeSingleTerm x
buildTerm (x:xs) 
  | x== TkAbs = absTerm xs
  | x== TkApp = appTerm xs
  | x== TkIf  = ifTerm xs
  | x== TkLPar = ParTerm (parCase xs)
  | (x== TkPlus)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntAdd (buildTerm (fst operands)) (buildTerm (snd operands))
  | (x== TkMinus)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntSub (buildTerm (fst operands)) (buildTerm (snd operands))
  | (x== TkMul)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntMul (buildTerm (fst operands)) (buildTerm (snd operands))
  | (x== TkDiv)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntDiv (buildTerm (fst operands)) (buildTerm (snd operands))
  | (x== TkNand)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntNand (buildTerm (fst operands)) (buildTerm (snd operands))
  | (x== TkEq)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntEq (buildTerm (fst operands)) (buildTerm (snd operands))
  | (x== TkLt)&&((head xs)==TkLPar) = 
    let operands = (caseHelper (parRemove xs) commaSeperated TkComma 0 [])
       in IntLt (buildTerm (fst operands)) (buildTerm (snd operands))
  | otherwise = error ("Undefined Term on token " ++ show x)

-- Helper function for the abs case
absTerm ::[Token] -> Term
absTerm xs = 
  let absCase = caseHelper (parRemove xs) [TkAbs] TkColon 0 []
      in let colDot = caseHelper (snd absCase) [TkAbs] TkFullStop 0 []
             in Abs (getVar (head(fst absCase))) (tokenType (fst colDot)) 
                  (buildTerm (snd colDot))

-- Helper function for the app case
appTerm ::[Token] -> Term
appTerm xs =
  let appCase = caseHelper (parRemove xs) commaSeperated TkComma 0 []
      in App (buildTerm (fst appCase)) (buildTerm (snd appCase)) 

-- Function removes the first and last parenthese of term or group of terms
parRemove :: [Token] -> [Token]
parRemove xs = if (((head xs)==TkLPar)&& ((last xs)==TkRPar)) 
      then (tail(init xs)) else error ("Mismatched parentheses")                     

-- Helper function for the if case
ifTerm ::[Token] -> Term
ifTerm xs = 
  let ifCase = caseHelper (ifFix xs) [TkIf] TkThen 0 []
      in let thenElse = caseHelper (snd ifCase) [TkIf] TkElse 0 []
             in If (buildTerm (fst ifCase)) (buildTerm (fst thenElse)) 
                  (buildTerm (snd thenElse))

-- Function checks for closing fi term for if functions
ifFix :: [Token] -> [Token]
ifFix xs = if (last xs == TkFi) then (init xs) else error ("missing fi")

-- Expression that contain multiple terms or types needs to be broken up 
-- at key points i.e. if cases seperate terms at the then and else tokens, 
-- however nested if cases are ignored via a counter such that the tokens are 
--  not partitioned at this point inside nested terms. 
caseHelper :: [Token] -> [Token] -> Token-> Int -> [Token]-> ([Token],[Token])
caseHelper [] tk0 _ _ _ = error ("Incomplete "++(show (head tk0))++ " statement")
caseHelper (x:xs) tk0 tk n ys | ((n==0) && (x== tk)) = (ys , xs)
                            | ((not(n==0)) && (x== tk)) = 
                              caseHelper xs tk0 tk (n-1) (ys++[x])
                            | x `elem` tk0 = caseHelper xs tk0 tk (n+1) (ys++[x])
                            | otherwise = caseHelper xs tk0 tk n (ys++[x])

-- Handles the ParTerm case
parCase ::[Token] -> Term
parCase xs = if (last xs == TkRPar) then (buildTerm (init xs)) 
      else error ("missing parentheses")

fv::Term->[Var]
fv (Var x)         = [x]
fv (Abs x _ t)     = [y |y<-(fv t), x/=y]
fv (If t1 t2 t3)   = (fv t1) ++ (fv t2) ++ (fv t3)
fv (ParTerm t)     = fv t
fv (App t1 t2)     = (fv t1)++(fv t2)
fv (IntAdd t1 t2)  = (fv t1)++(fv t2)
fv (IntSub t1 t2)  = (fv t1)++(fv t2)
fv (IntMul t1 t2)  = (fv t1)++(fv t2)
fv (IntDiv t1 t2)  = (fv t1)++(fv t2)
fv (IntNand t1 t2) = (fv t1)++(fv t2)
fv (IntEq t1 t2)   = (fv t1)++(fv t2)
fv (IntLt t1 t2)   = (fv t1)++(fv t2)
fv _               = []

-- Checking the free variables prevents overwriting an inner abstraction 
-- variable name when that variable is set from its innermost lambda
subst:: Var -> Term -> Term -> Term
subst x s t = if(elem x (fv t)) then subHelper x s t else t

-- Abs case already checked for free variables,
subHelper:: Var -> Term -> Term -> Term 
subHelper x s (Var y)        = if (y==x) then s else (Var y)
subHelper x s (Abs y tp t)   = Abs y tp (subHelper x s t) 
subHelper x s (App t1 t2)    = App (subst x s t1) (subst x s t2)
subHelper x s (If t1 t2 t3)  = If (subst x s t1) (subst x s t2) (subst x s t3)
subHelper x s (IntAdd t1 t2) = IntAdd (subst x s t1) (subst x s t2)
subHelper x s (IntSub t1 t2) = IntSub (subst x s t1) (subst x s t2)
subHelper x s (IntMul t1 t2) = IntMul (subst x s t1) (subst x s t2)
subHelper x s (IntDiv t1 t2) = IntDiv (subst x s t1) (subst x s t2)
subHelper x s (IntNand t1 t2)= IntNand (subst x s t1) (subst x s t2)
subHelper x s (IntEq t1 t2)  = IntEq (subst x s t1) (subst x s t2)
subHelper x s (IntLt t1 t2)  = IntLt (subst x s t1) (subst x s t2)
subHelper x s (ParTerm t)    = ParTerm (subHelper x s t)
subHelper _ _ z              = z

isValue:: Term -> Bool
isValue (Abs _ _ _) = True
isValue Tru         = True
isValue Fls         = True
isValue (IntConst _)= True
isValue _           = False
\end{code}
