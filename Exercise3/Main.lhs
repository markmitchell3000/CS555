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

Code:
%\newpage
%include DeBruijn.lhs

\subsection{3.2 Natural Semantics with Nameless Terms}
\label{sec:core}

This is very similar to the previous Natural semantics but our values now 
uses closures in place of abstractions.  This allows us to carry variable values
in our environment rather than calling a substitution function.  Since this uses
DeBruijn terms rather than variable names we can use these as indices of the 
environment to locate the values of our variables.  

Code:
%\newpage
%include NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices.lhs

\subsection{3.3 CES Machine}
\label{sec:core}

CES machine is a 3 tuple of code, environment, stack.  Intermediate code is 
created from the debruijin term given.  The environment is used to track free 
variables just as it was in the nameless natural semantics.  The stack is used 
to store the continuation of the program, similar to the CEK machine.

Source code:
%\newpage
%include CESMachine.lhs

\subsection{3.4 Continuation Passing Style (CPS)}
\label{sec:core}

By converting our term/program to CPS control is passed explicitly in the form 
of a continuation. 

Code:
%\newpage
%include CPS.lhs

\subsection{3.5 CE3R Machine}
\label{sec:core}

The CE3R Machine is similar to the CES machine with code and environment but 
this is a stackless machine using 3 register to handle its reductions.  A CPS 
converted term is sent to the Debruijn code so that the variables can lookup 
their respective values by index in the environment.

Code:
%\newpage
%include CE3RMachine.lhs

%\newpage
Main program 
Code:

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
  putStrLn ("---Evaluation of CPS using CE3R Small Step Semantics:---")
  let ce3rTerm = CR.eval (DB.toDeBruijn cpsTerm)
  putStrLn $ show ce3rTerm

\end{code}

\subsection{3.6 Test Cases}
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
let iseven = let mod = abs(m:Int.abs(n:Int.-(m,*(n,/(m,n))))) in abs(k:Int.
=(0,app(app(mod,k),2))) end in app(iseven,7)
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
---De Bruijn Notation:---
let let abs(Int.abs(Int.-(~1,*(~0,/(~1,~0))))) in abs(Int.
=(0,app(app(~1,~0),2))) end in app(~0,7) end
---Natural semantics using DeBruijn Terms:---
BoolVal False
---CESMachine - Normal form:---
BoolVal False
---Continuation Passing Style (CPS):---
app(abs(k:Bool.app(abs(k:Bool.app(k,abs(iseven:Bool.abs(k:Bool.app(abs(k:Bool.
app(k,iseven)),abs(v1:Bool.app(abs(k:Bool.app(k,7)),abs(v2:Bool.app(app(v1,v2),
k))))))))),abs(v1:Bool.app(abs(k:Bool.app(abs(k:Bool.app(k,abs(mod:Bool.abs(k`:
Bool.app(k`,abs(k:Int.abs(k`:Bool.app(abs(k:Bool.app(k,0)),abs(v1:Int.app(abs(k`
:Bool.app(abs(k`:Bool.app(abs(k:Bool.app(k,mod)),abs(v1:Bool.app(abs(k`:Bool.app
(k`,k)),abs(v2:Bool.app(app(v1,v2),k`)))))),abs(v1:Bool.app(abs(k:Bool.app(k,2))
,abs(v2:Bool.app(app(v1,v2),k`)))))),abs(v2:Int.app(k`,=(v1,v2))))))))))))),abs
(v1:Bool.app(abs(k:Bool.app(k,abs(m:Int.abs(k:Bool.app(k,abs(n:Int.abs(k:Bool.
app(abs(k:Bool.app(k,m)),abs(v1:Int.app(abs(k:Bool.app(abs(k:Bool.app(k,n)),abs
(v1:Int.app(abs(k:Bool.app(abs(k:Bool.app(k,m)),abs(v1:Int.app(abs(k:Bool.app
(k,n)),abs(v2:Int.app(k,/(v1,v2))))))),abs(v2:Int.app(k,*(v1,v2))))))),abs(v2:
Int.app(k,-(v1,v2))))))))))))),abs(v2:Bool.app(app(v1,v2),k)))))),abs(v2:Bool.
app(app(v1,v2),k)))))),abs(a:Bool.a))
---Evaluation of CPS using CE3R Small Step Semantics:---
BoolVal False


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
---De Bruijn Notation:---
app(fix abs(->(Int,Bool).abs(Int.if =(0,~0) then true else if =(0,-(~0,1)) 
then false else app(~1,-(~0,2)) fi fi)),7)
---Natural semantics using DeBruijn Terms:---
BoolVal False
---CESMachine - Normal form:---
BoolVal False
---Continuation Passing Style (CPS):---
app(abs(k:Bool.app(abs(f':Bool.app(abs(k:Bool.app(abs(k:Bool.app(k,f')),abs(v1:
Bool.app(abs(k:Bool.app(k,7)),abs(v2:Bool.app(app(v1,v2),k)))))),k)),fix abs(ie:
Bool.abs(x:Bool.abs(kf:Bool.app(abs(k:Bool.app(abs(k:Bool.app(abs(k:Bool.app
(k,0)),abs(v1:Int.app(abs(k:Bool.app(k,x)),abs(v2:Int.app(k,=(v1,v2))))))),abs
(v1:Bool.app(if v1 then abs(k:Bool.app(k,true)) else abs(k:Bool.app(abs(k:Bool.
app(abs(k:Bool.app(k,0)),abs(v1:Int.app(abs(k:Bool.app(abs(k:Bool.app(k,x)),abs
(v1:Int.app(abs(k:Bool.app(k,1)),abs(v2:Int.app(k,-(v1,v2))))))),abs(v2:Int.app
(k,=(v1,v2))))))),abs(v1:Bool.app(if v1 then abs(k:Bool.app(k,false)) else abs
(k:Bool.app(abs(k:Bool.app(k,ie)),abs(v1:Bool.app(abs(k:Bool.app(abs(k:Bool.app
(k,x)),abs(v1:Int.app(abs(k:Bool.app(k,2)),abs(v2:Int.app(k,-(v1,v2))))))),abs
(v2:Bool.app(app(v1,v2),k)))))) fi,k)))) fi,k)))),abs(v1:Bool.app(kf,v1)))))))),
abs(a:Bool.a))
---Evaluation of CPS using CE3R Small Step Semantics:---
BoolVal False


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
---De Bruijn Notation:---
app(app(fix abs(->(Int,->(Int,Int)).abs(Int.abs(Int.if =(0,~0) then 1 else 
*(~1,app(app(~2,~1),-(~0,1))) fi))),2),3)
---Natural semantics using DeBruijn Terms:---
IntVal 8
---CESMachine - Normal form:---
IntVal 8
---Continuation Passing Style (CPS):---
app(abs(k:Int.app(abs(k:Int.app(abs(f':Int.app(abs(k:Int.app(abs(k:Int.app
(k,f')),abs(v1:Int.app(abs(k:Int.app(k,2)),abs(v2:Int.app(app(v1,v2),k)))))),k))
,fix abs(e:Int.abs(x:Int.abs(kf:Int.app(abs(k:Int.app(k,abs(y:Int.abs(k:Int.app
(abs(k:Int.app(abs(k:Int.app(k,0)),abs(v1:Int.app(abs(k:Int.app(k,y)),abs(v2:Int
.app(k,=(v1,v2))))))),abs(v1:Int.app(if v1 then abs(k:Int.app(k,1)) else abs
(k:Int.app(abs(k:Int.app(k,x)),abs(v1:Int.app(abs(k:Int.app(abs(k:Int.app(abs
(k:Int.app(k,e)),abs(v1:Int.app(abs(k:Int.app(k,x)),abs(v2:Int.app(app(v1,v2),k)
))))),abs(v1:Int.app(abs(k:Int.app(abs(k:Int.app(k,y)),abs(v1:Int.app(abs(k:Int.
app(k,1)),abs(v2:Int.app(k,-(v1,v2))))))),abs(v2:Int.app(app(v1,v2),k)))))),abs
(v2:Int.app(k,*(v1,v2))))))) fi,k))))))),abs(v1:Int.app(kf,v1)))))))),abs(v1:Int
.app(abs(k:Int.app(k,3)),abs(v2:Int.app(app(v1,v2),k)))))),abs(a:Int.a))
---Evaluation of CPS using CE3R Small Step Semantics:---
IntVal 8


Test Case 4:

---Input:---
app (fix (abs (f:->(Int,Int). abs (x: Int. if =(0,x) then 1 else
*(x, app(f, -(x,1))) fi))), app (fix (abs (f:->(Int,Int).
abs (x: Int. if =(0,x) then 1 else *(x, app(f, -(x,1))) fi))), 3))
---Term:---
app(fix abs(f:->(Int,Int).abs(x:Int.if =(0,x) then 1 else *(x,app(f,-(x,1))) 
fi)),app(fix abs(f:->(Int,Int).abs(x:Int.if =(0,x) then 1 else *(x,app(f,-(x,1)
)) fi)),3))
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
---De Bruijn Notation:---
app(fix abs(->(Int,Int).abs(Int.if =(0,~0) then 1 else *(~0,app(~1,-(~0,1))) 
fi)),app(fix abs(->(Int,Int).abs(Int.if =(0,~0) then 1 else *(~0,app(~1,-(~0,1)
)) fi)),3))
---Natural semantics using DeBruijn Terms:---
IntVal 720
---CESMachine - Normal form:---
IntVal 720
---Continuation Passing Style (CPS):---
app(abs(k:Int.app(abs(f':Int.app(abs(k:Int.app(abs(k:Int.app(k,f')),abs(v1:Int.
app(abs(k:Int.app(abs(f':Int.app(abs(k:Int.app(abs(k:Int.app(k,f')),abs(v1:Int.
app(abs(k:Int.app(k,3)),abs(v2:Int.app(app(v1,v2),k)))))),k)),fix abs(f:Int.abs
(x:Int.abs(kf:Int.app(abs(k:Int.app(abs(k:Int.app(abs(k:Int.app(k,0)),abs(v1:Int
.app(abs(k:Int.app(k,x)),abs(v2:Int.app(k,=(v1,v2))))))),abs(v1:Int.app(if v1 
then abs(k:Int.app(k,1)) else abs(k:Int.app(abs(k:Int.app(k,x)),abs(v1:Int.app
(abs(k:Int.app(abs(k:Int.app(k,f)),abs(v1:Int.app(abs(k:Int.app(abs(k:Int.app
(k,x)),abs(v1:Int.app(abs(k:Int.app(k,1)),abs(v2:Int.app(k,-(v1,v2))))))),abs
(v2:Int.app(app(v1,v2),k)))))),abs(v2:Int.app(k,*(v1,v2))))))) fi,k)))),abs
(v1:Int.app(kf,v1)))))))),abs(v2:Int.app(app(v1,v2),k)))))),k)),fix abs(f:Int.
abs(x:Int.abs(kf:Int.app(abs(k:Int.app(abs(k:Int.app(abs(k:Int.app(k,0)),abs
(v1:Int.app(abs(k:Int.app(k,x)),abs(v2:Int.app(k,=(v1,v2))))))),abs(v1:Int.app
(if v1 then abs(k:Int.app(k,1)) else abs(k:Int.app(abs(k:Int.app(k,x)),abs
(v1:Int.app(abs(k:Int.app(abs(k:Int.app(k,f)),abs(v1:Int.app(abs(k:Int.app(abs
(k:Int.app(k,x)),abs(v1:Int.app(abs(k:Int.app(k,1)),abs(v2:Int.app(k,-(v1,v2))))
))),abs(v2:Int.app(app(v1,v2),k)))))),abs(v2:Int.app(k,*(v1,v2))))))) fi,k)))),
abs(v1:Int.app(kf,v1)))))))),abs(a:Int.a))
---Evaluation of CPS using CE3R Small Step Semantics:---
IntVal 720

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
=(1,x) then false else app(ie,-(x,2)) fi fi)) in let collatz = fix abs(collatz:
->(Int,Int).abs(x:Int.if app(iseven,x) then app(collatz,/(x,2)) else if =(x,1) 
then 1 else app(collatz,+(*(3,x),1)) fi fi)) in app(collatz,1000) end end
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
---De Bruijn Notation:---
let fix abs(->(Int,Bool).abs(Int.if =(0,~0) then true else if =(1,~0) then false
 else app(~1,-(~0,2)) fi fi)) in let fix abs(->(Int,Int).abs(Int.if app(~2,~0) 
 then app(~1,/(~0,2)) else if =(~0,1) then 1 else app(~1,+(*(3,~0),1)) fi fi)) 
 in app(~0,1000) end end
---Natural semantics using DeBruijn Terms:---
IntVal 1
---CESMachine - Normal form:---
IntVal 1
---Continuation Passing Style (CPS):---
app(abs(k:Int.let iseven = fix abs(ie:Int.abs(x:Int.abs(kf:Int.app(abs(k:Int.app
(abs(k:Int.app(abs(k:Int.app(k,0)),abs(v1:Int.app(abs(k:Int.app(k,x)),abs(v2:
Int.app(k,=(v1,v2))))))),abs(v1:Int.app(if v1 then abs(k:Int.app(k,true)) else 
abs(k:Int.app(abs(k:Int.app(abs(k:Int.app(k,1)),abs(v1:Int.app(abs(k:Int.app
(k,x)),abs(v2:Int.app(k,=(v1,v2))))))),abs(v1:Int.app(if v1 then abs(k:Int.app
(k,false)) else abs(k:Int.app(abs(k:Int.app(k,ie)),abs(v1:Int.app(abs(k:Int.app
(abs(k:Int.app(k,x)),abs(v1:Int.app(abs(k:Int.app(k,2)),abs(v2:Int.app(k,
-(v1,v2))))))),abs(v2:Int.app(app(v1,v2),k)))))) fi,k)))) fi,k)))),abs(v1:Int.
app(kf,v1)))))) in app(abs(k:Int.let collatz = fix abs(collatz:Int.abs(x:Int.
abs(kf:Int.app(abs(k:Int.app(abs(k:Int.app(abs(k:Int.app(k,iseven)),abs(v1:Int.
app(abs(k:Int.app(k,x)),abs(v2:Int.app(app(v1,v2),k)))))),abs(v1:Int.app(if v1 
then abs(k:Int.app(abs(k:Int.app(k,collatz)),abs(v1:Int.app(abs(k:Int.app(abs
(k:Int.app(k,x)),abs(v1:Int.app(abs(k:Int.app(k,2)),abs(v2:Int.app(k,/(v1,v2))))
))),abs(v2:Int.app(app(v1,v2),k)))))) else abs(k:Int.app(abs(k:Int.app(abs(k:Int
.app(k,x)),abs(v1:Int.app(abs(k:Int.app(k,1)),abs(v2:Int.app(k,=(v1,v2))))))),
abs(v1:Int.app(if v1 then abs(k:Int.app(k,1)) else abs(k:Int.app(abs(k:Int.app
(k,collatz)),abs(v1:Int.app(abs(k:Int.app(abs(k:Int.app(abs(k:Int.app(k,3)),abs
(v1:Int.app(abs(k:Int.app(k,x)),abs(v2:Int.app(k,*(v1,v2))))))),abs(v1:Int.app
(abs(k:Int.app(k,1)),abs(v2:Int.app(k,+(v1,v2))))))),abs(v2:Int.app(app(v1,v2)
,k)))))) fi,k)))) fi,k)))),abs(v1:Int.app(kf,v1)))))) in app(abs(k:Int.app(abs
(k:Int.app(k,collatz)),abs(v1:Int.app(abs(k:Int.app(k,1000)),abs(v2:Int.app(app
(v1,v2),k)))))),k) end),k) end),abs(a:Int.a))
---Evaluation of CPS using CE3R Small Step Semantics:---
IntVal 1
\end{verbatim}

\end{document}


