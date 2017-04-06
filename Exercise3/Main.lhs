%% Literate Haskell script intended for lhs2TeX.

\documentclass[10pt]{article}
%include polycode.fmt


%format union = "\cup"
%format `union` = "\cup"
%format Hole = "\square"
%format MachineTerminate ="\varodot"
%format CEKMachineTerminate ="\varodot"
%format alpha = "\alpha"
%format gamma = "\gamma"
%format zeta = "\zeta"
%format kappa = "\kappa"
%format kappa'
%format capGamma = "\Gamma"
%format sigma = "\sigma"
%format tau = "\tau"
%format taus = "\tau s"
%format ltaus = "l\tau s"
%format tau1
%format tau1'
%format tau2
%format tau11
%format tau12
%format upsilon = "\upsilon"
%format xi = "\xi"
%format t12
%format t1
%format t1'
%format t2
%format t2'
%format t3
%format nv1

\usepackage{fullpage}
\usepackage{mathpazo}
\usepackage{graphicx}
\usepackage{color}
\usepackage[centertags]{amsmath}
\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{stmaryrd}
\usepackage{soul}
\usepackage{url}







\usepackage{vmargin}
\setpapersize{USletter}
\setmarginsrb{1.1in}{1.0in}{1.1in}{0.6in}{0.3in}{0.3in}{0.0in}{0.2in}
\parindent 0in  \setlength{\parindent}{0in}  \setlength{\parskip}{1ex}

\usepackage{epsfig}\usepackage{rotating}

\usepackage{mathpazo,amsmath,amssymb}
\pagestyle{myheadings}
\title{CS555 Advanced Compilers}
\author{Mark Mitchell, Doug Keating}
\date{March 26, 2017}

\begin{document}
\setcounter{section}{1}

\section*{Mark Mitchell, Doug Keating}
\section*{Exercise 2}

\subsection{2.1 Enriching the core lambda language}
\label{sec:core}

We updated our parser and interpreters so that it can handle let expressions and
general recursion using the fix operator.

(Small-Step) Structural Operational Semantics Rules:
Additional rules for let and fix have been added to the core lambda language.
\begin{verbatim}
Terms
     a, b ::= \x.a | a1a2| x | c | bool | if a1 a2 a3|op(a1, a2)
Constants
     c ::= |-4294967296|...|-1|0|1|2|...|4294967296|
Booleans
     bool ::= tru|fls 
Operators
     op ::= +|-|*|/|NAND|==|<
Values
     v :: c | bool |\x.a

Small step evaluation rules:

  T-App1
       a -> a'
       ---------
       ab -> a'b
  T-App2
       b -> b'
       --------
       vb -> vb'
  T-Abs
       ---------------------
       (\x.a)v -> [x |-> v]a
  T-If1
       a -> a'
       -------------------------
       if a b1 b2 -> if a' b1 b2
  T-IfTru
      ---------------
      if tru a b -> a
  T-IfFls
      ---------------
      if fls a b -> b
  T-Op1
       a -> a'
       -------------------
       op(a,b) -> op(a',b)
  T-Op2
       b -> b'
       -------------------
       op(v,b) -> op(v,b')
  T-Op3
       ------------------- (where v = ~op(n1, n2))
       op(c1,c2) -> v
       * v is a bool for op's ==, < and a constant otherwise
  T-Let1
       a -> a'
       -----------------------
       Let x=a in b -> Let x=a' in b
  T-Let2
       ---------------------------
       Let x=v in b -> [x |-> v] b
  T-Fix1
       a -> a'
       -------------------- 
       Fix a -> Fix a'
  T-Fix2
       -------------------------------------- 
       Fix (\x.a) -> [x |-> Fix (\x.a)](\x.a)

\end{verbatim}

(Big-Step)Natural semantics Rules:
These have been extended to include the let and fix cases.
\begin{verbatim}
Big step evaluation rules:
   T-TermValue
       a => v
   T-Constant
       c => c
   T-Abstraction
       \x.a => \x.a
   T-Application
       a => \x.a'  b => v'  [x|->v']a'=>v
       ----------------------------------
                     ab => v
   T-IfTruN
       a => tru  b1 => v
       -----------------
       if a b1 b2 => v
   T-IfFlsN
       a => fls  b2 => v
       -----------------
       if a b1 b2 => v
   T-OpN
       a1 => v1  a2 => v2  v = ~op(v1, v2)
       -----------------------------------
                 op(a1, a2) => v
   T-LetN
       a=>v' [x|-> v']b => v
       ---------------------
       Let x=a in b => v
   T-FixN
       a=>(\x.a') Fix (\x.a')=> [x |-> Fix (\x.a')](\x.a')
       ---------------------------------------------------
       Fix a => [x |-> Fix (\x.a')](\x.a')
  
\end{verbatim}

Formal Typing Rules:
These typing rules include the core lambda calculus and the extended terms let 
and fix.
\begin{verbatim}
Types
       T ::= T->T | Int | Bool
Environments
       e ::= [] | e, x:T 
Constants/Integers
     c ::= |-4294967296|...|-1|0|1|2|...|4294967296|
OpNum
     opN ::= +|-|*|/|Nand
OpBool
     opB ::= eq|lt

Typing rules:
   Type-Base
       e |- t:T
   Type-Var
       x:T 'member' e
       ------------
       e |- x:T
   Type-Abs
       e, x:T |- t:T' x 'not amember' dom (e)
       -------------------------------------
       e |- \x:T.t : T->T'
    Type-App
       e |- t1: T->T',  e|- t2:T
       ------------------------
       e |- t1 t2 :T'
    Type-Int
       -----------
       e |- c: Int
    Type-BoolTrue
       ---------------
       e |- true: Bool
    Type-BoolFalse
       ----------------
       e |- false: Bool
    Type-Conditional
       e |- t1:Bool,   e |- t2:T,  e |- t3:T
       -----------------------------------
       e |- if t1 then t2 else t3 : T
    Type-OpNum
       e |- t1:Int,  e |- t2:Int
       ------------------------(opN is +|-|*|/|Nand)
       e |- opN (t1, t2): Int
    Type-OpBool
       e |- t1:Int,  e |- t2:Int
       ------------------------(opB is eq|lt)
       e |- opB (t1, t2): Bool
    Type-Let
       e |- t1:T, e, x:T |-t2:T' x 'not a member' dom(e)
       -------------------------------------------------
       e |- let x=t1 in t2 :T'
    Type-Fix
       e |- t: T->T
       -------------
       e |- fix t: T    
  
\end{verbatim}

%\newpage
Parsing:
This is the parser updated to read this language:

%\newpage
%include AbstractSyntax.lhs


%\newpage
Updated Structural operational semantics:
This is the code used to express the small-step semantics. 

%\newpage
%include StructuralOperationalSemantics.lhs

Updated Natural semantics:
The natural semantics is very similar to the structural operational semantics 
but instead of using single step evaluation it uses big step evaluation which 
allows for terms to be reduced without returning the program to the root of the 
evaluation tree.  Effectively natural semantics allow for evaluation to occur 
nearby to where the most work has been done.  We implemented this code for 
Natural Semantics.

Source code:
%\newpage
%include NaturalSemantics.lhs

%\newpage
Arithmetic:
This is the same code used in exercise 1.   

Source code:
%\newpage
%include IntegerArithmetic.lhs

%\newpage
Type checker:
We used the provided code for type checking for the core lambda language and 
then extended it for the let and fix operations.

Source code:

%\newpage
%include Typing.lhs

%\newpage
Main program:
Our main program reads from a text file a string, this is sent to the parser to 
be tokenized and converted to a term.  This term is type checked to see if the 
entire program can be interpreted.  Then the term is sent to the updated 
small-step and big-step evaluation modules, following this the 
reductionSemantics, CCMachine, SCCMachine, CKMachine, and the CEKMachine are 
called.  The reduction semantics, CC Machine and SCC machine all use a context
to handle reductions.  All of these modules produce the same term in the test 
cases provided at the bottom. 

The reduction semantics returns an updated term and rebuilds its context for 
every reduction.  The CC and SCC machines carry the context along with the 
current term to be reduced, this allows the reductions to be handled down inside
the context tree.  However the context tree must be recursed through when it is 
updated so that a new context will reflect the most recent reduction.  The CK 
and CEK machines do not need to do this sort of recursive decent through the 
program.  By using the continuation structure all reductions are effectively 
done inside of the context of whatever structure is at the head of a list of 
program instructions.  This is far more effective as the program can be updated 
in constant time once a term is reduced.  

Source code:

\begin{code}
import System.Environment
import Data.Char
import qualified Typing as T
import qualified AbstractSyntax as S
import qualified StructuralOperationalSemantics as O
import qualified NaturalSemantics as N
import qualified ReductionSemantics as R
import qualified CCMachine as C
import qualified SCCMachine as D
import qualified CKMachine as K
import qualified CEKMachine as L
import qualified DeBruijn as DB
import qualified NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices as Z
import qualified CPS as CP

main = do
  args <- getArgs
  str <- mapM readFile args
  putStrLn "---Input:---"
  putStrLn (head str)
  putStrLn "---Term:---"
  let tokens = (S.makeTokens (head str))
  let term = S.buildTerm tokens
  putStrLn $ show term
  putStrLn "---Type:---"
  let exprType = T.typeCheck term
  putStrLn $ show exprType
  putStrLn "---Structural Semanitcs - Normal form:---"
  let newTerm1 = O.eval term
  putStrLn $ show newTerm1
  putStrLn "---Natural Semanitcs - Normal form:---"
  let newTerm2 = N.eval term
  putStrLn $ show newTerm2
  putStrLn "---Reduction Semantics - Normal form:---"
  let newTerm3 = R.textualMachineEval term
  putStrLn $ show newTerm3
  putStrLn "---CCMachine - Normal form:---"
  let newTerm4 = C.ccMachineEval term
  putStrLn $ show newTerm4
  putStrLn "---SCCMachine - Normal form:---"
  let newTerm5 = D.sccMachineEval term
  putStrLn $ show newTerm5
  putStrLn "---CKMachine - Normal form:---"
  let newTerm6 = K.ckMachineEval term
  putStrLn $ show newTerm6
  putStrLn "---CEKMachine - Normal form:---"
  let newTerm7 = L.cekMachineEval term
  putStrLn $ show newTerm7
  putStrLn "---De Bruijn Notation:---"
  let dBTerm = DB.toDeBruijn term
  putStrLn $ show dBTerm
  putStrLn ("---Natural semantics using DeBruijn Terms:---")
  let dbTerm1 = Z.eval dBTerm
  putStrLn $ show dbTerm1
  putStrLn ("---Continuation Passing Style (CPS):---")
  let cpsTerm = CP.toCPS exprType term
  let cpsTerm' = O.eval (S.App cpsTerm (S.Abs "a" 
                          (S.TypeArrow exprType exprType) (S.Var "a")))
  putStrLn $ show cpsTerm
  putStrLn ("---Evaluation of CPS using Small Step Semantics:---")
  putStrLn $ show cpsTerm'

\end{code}

\subsection{2.2 Reduction Semantics}
\label{sec:core}
2.2.1 Evaluation Contexts:

The following code was used to implement evaluation contexts:

%\newpage
%include EvaluationContext.lhs

%\newpage
2.2.2 Standard Reduction:

When forming the evaluation contexts, if a term is a redex, then it should
be the next thing reduced.  Otherwise the first subterm that is not a value
should be searched for a redex.  In our implementation this is accomplished 
by returning the evaluation context (Term, E.Hole) if the term is a redexe. 
Otherwise, the first non-value subterm is passed to a helper function that uses 
makeEvalContext and E.fillWithContext to recursively search for a redex within
 that subterm to reduce. makeContractum is responsible for reducing the redex once
 it is found.
 
 
The textual machine recursively evaluates a term, splitting it into an evaluation
 context and a subterm.  If this subterm is a redex, it is reduced to obtain 
 a contractum, and the evaluation context is filled with this contractum. This 
 machine is inherently inefficient, since it essentially returns to the root of 
 the tree and then searches for the location of the next redex.  This does not 
 provide  any means of localization that could enhance efficiency.

 
%\newpage
%include ReductionSemantics.lhs

%\newpage

\subsection{2.3 Abstract register machines}
\label{sec:core}
2.3.1 CCMachine
This machine builds a context tree which is a copy of the program with a hole 
located where the current reduction is being handled.  Once the term is reduced 
its relative context will have further terms extracted and then reduced, and 
the context tree is rebuilt to reflect the structure surrounding these 
reductions.  Updating the context after a reduction is a little tricky because 
the context tree will be almost the same one level above the current reduction, 
inside this level a new context will be added as a child or a hole will be used 
because the next reduction will be handled on this level or a different branch 
of this level.   
%\newpage
%include CCMachine.lhs

%\newpage
2.3.2 SCCMachine
Very similar to the CCMachine, this machine however will look at the context 
once a term is reduced to a value in order to decide what to do next.  This 
allows for applications and operations to be done immediately once the terms 
needed are reduced to values.  This does the same thing as the CCMachine but it 
combines steps which make its evaluation much simpler.    
%\newpage
%include SCCMachine.lhs

%\newpage
2.3.3 CKMachine
This machine does something similar to the CC and SCC machines but this uses a 
continuation structure rather then a context tree.  Allowing for the machine to 
use the head of the contiuation structure when a reduction is done, instead of 
requiring that the context tree be traversed in order for the programs state to 
be updated. 
%\newpage
%include CKMachine.lhs

%\newpage
2.3.4 CEKMachine
The CEKMachine builds upon the CKMachine by adding closure and environment this 
allows for variables to be updated as the terms are being reduced rather than 
calling a recursive substitution function.  The environment fuctions as a lookup 
table that is only called when a value is required for a variable.
%\newpage
%include CEKMachine.lhs

%\newpage
\subsection{2.4 Test Cases}
\label{sec:core}
\begin{verbatim}
Test Case 1:

---Input:---
let
  iseven =
    let
      mod = abs (m:Int. abs (n:Int. -(m,*(n,/(m,n)))))
    in
      abs (k:Int. =(0, app(app(mod,k),2)))
    end
in
  app (iseven, 7)
end
---Term:---
let iseven = let mod = abs(m:Int.abs(n:Int.-(m,*(n,/(m,n))))) in abs(k:Int.=
(0,app(app(mod,k),2))) end in app(iseven,7)
end
---Type:---
Bool
---Structural Semanitcs - Normal form:---
false
---Natural Semanitcs - Normal form:---
false
---Reduction Semantics - Normal form:---
false
---CCMachine - Normal form:---
false
---SCCMachine - Normal form:---
false
---CKMachine - Normal form:---
false
---CEKMachine - Normal form:---
false

Test Case 2:

---Input:---
app (fix (abs (ie:->(Int,Bool). abs (x:Int. if =(0,x) then true else
if =(0, -(x,1)) then false else app (ie, -(x,2)) fi fi))), 7)
---Term:---
app(fix abs(ie:->(Int,Bool).abs(x:Int.if =(0,x) then true else if =(0,-(x,1)) 
then false else app(ie,-(x,2)) fi fi)),7)
---Type:---
Bool
---Structural Semanitcs - Normal form:---
false
---Natural Semanitcs - Normal form:---
false
---Reduction Semantics - Normal form:---
false
---CCMachine - Normal form:---
false
---SCCMachine - Normal form:---
false
---CKMachine - Normal form:---
false
---CEKMachine - Normal form:---
false

Test Case 3:

---Input:---
app (app (fix (abs (e:->(Int,->(Int,Int)). abs (x:Int. abs (y: Int.
if =(0,y) then 1 else *(x,app(app(e,x),-(y,1))) fi)))), 2), 3)
---Term:---
app(app(fix abs(e:->(Int,->(Int,Int)).abs(x:Int.abs(y:Int.if =(0,y) then 1 else 
*(x,app(app(e,x),-(y,1))) fi))),2),3)
---Type:---
Int
---Structural Semanitcs - Normal form:---
8
---Natural Semanitcs - Normal form:---
8
---Reduction Semantics - Normal form:---
8
---CCMachine - Normal form:---
8
---SCCMachine - Normal form:---
8
---CKMachine - Normal form:---
8
---CEKMachine - Normal form:---
8

Test Case 4:

---Input:---
app (fix (abs (f:->(Int,Int). abs (x: Int. if =(0,x) then 1 else
*(x, app(f, -(x,1))) fi))), app (fix (abs (f:->(Int,Int).
abs (x: Int. if =(0,x) then 1 else *(x, app(f, -(x,1))) fi))), 3))
---Term:---
app(fix abs(f:->(Int,Int).abs(x:Int.if =(0,x) then 1 else *(x,app(f,-(x,1))) 
fi)),app(fix abs(f:->(Int,Int).abs(x:Int.if
 =(0,x) then 1 else *(x,app(f,-(x,1))) fi)),3))
---Type:---
Int
---Structural Semanitcs - Normal form:---
720
---Natural Semanitcs - Normal form:---
720
---Reduction Semantics - Normal form:---
720
---CCMachine - Normal form:---
720
---SCCMachine - Normal form:---
720
---CKMachine - Normal form:---
720
---CEKMachine - Normal form:---
720

Test Case 5:

---Input:---
let
   iseven = fix (abs (ie:->(Int,Bool). abs (x:Int.
              if =(0,x) then true else
                if =(1,x) then false else
                  app (ie, -(x,2)) fi fi)))
in
  let
    collatz = fix (abs (collatz:->(Int,Int). abs (x: Int.
                if app (iseven, x) then app (collatz, /(x,2)) else
                  if =(x,1) then 1 else
                    app (collatz, +(*(3,x),1)) fi fi)))
  in
    app (collatz, 1000)
  end
end
---Term:---
let iseven = fix abs(ie:->(Int,Bool).abs(x:Int.if =(0,x) then true else if 
=(1,x) then false else app(ie,-(x,2)) fi fi))
 in let collatz = fix abs(collatz:->(Int,Int).abs(x:Int.if app(iseven,x) then 
 app(collatz,/(x,2)) else if =(x,1) then 1
else app(collatz,+(*(3,x),1)) fi fi)) in app(collatz,1000) end end
---Type:---
Int
---Structural Semanitcs - Normal form:---
1
---Natural Semanitcs - Normal form:---
1
---Reduction Semantics - Normal form:---
1
---CCMachine - Normal form:---
1
---SCCMachine - Normal form:---
1
---CKMachine - Normal form:---
1
---CEKMachine - Normal form:---
1
\end{verbatim}
\end{document}


