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
\date{April 20, 2017}

\begin{document}
\setcounter{section}{1}

\section*{Mark Mitchell, Doug Keating}
\section*{Exercise 3}

\subsection{3.1 De Bruijn Notation}
\label{sec:core}

De Bruijn notation is exactly the same as our previous notation byt with one key
difference, all variable names are changed to integers that represent indices.  
This index tells where to get the variable value form a list of values.  If the 
variable is bound to the innermost lambda expression the variable will get its 
value from the head of the list or index 0.  If the variable is a free variable 
in the innermost lambda expression then the index will be used to find this 
value in the list, the more lambda nested the variable, the higher the index.  


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
import qualified CESMachine as CES
import qualified CPS as CP
import qualified CE3RMachine as CR

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
  putStrLn ("---CESMachine - Normal form:---")
  let newTerm8 = CES.eval dBTerm
  putStrLn $ show newTerm8
  putStrLn ("---Continuation Passing Style (CPS):---")
  let cpsTerm = S.App (CP.toCPS exprType term) (S.Abs "a" exprType (S.Var "a"))
  putStrLn $ show cpsTerm
  --putStrLn ("---Evaluation of CPS using Small Step Semantics:---")
  --let smTerm = O.eval (cpsTerm)
  --putStrLn $ show smTerm
  putStrLn ("---Evaluation of CPS using CE3R Small Step Semantics:---")
  let ce3rTerm = CR.eval (DB.toDeBruijn cpsTerm)
  putStrLn $ show ce3rTerm

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


