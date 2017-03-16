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
\date{February 28, 2017}

\begin{document}
\setcounter{section}{1}

\section*{Mark Mitchell, Doug Keating}
\section*{Exercise 1}

\subsection{Core lambda language}
\label{sec:core}

We implemented this project using a small core lambda language, with booleans, 
integers and arithmetic operators.  The implementation of the concrete syntax 
and the terminal symbols (tokens) used in the grammar can be found in the 
AbstractSyntax code.

%\newpage
\subsection{Parsing}
Here is the parser built to read this language:

%\newpage
%include AbstractSyntax.lhs


%\newpage
\subsection{Binding and free variables}
As seen above their is code to enumerate free variables, substitute terms, and 
verify that the term has been reduced to a value.  These can be found in the 
functions fv, subst and isValue.

%\newpage
\subsection{Structural operational semantics}
This is the code used to express the small-step semantics. 

%\newpage
%include StructuralOperationalSemantics.lhs

%\newpage
\subsection{Arithmetic}
The module |IntegerArithmetic| use the 32-bit 2's complement range, and the 
arithmetic operations addition, subtraction, multiplication, division, NAND, 
equality and the less than comparison of two integers.   

Source code:
%\newpage
%include IntegerArithmetic.lhs

%\newpage
\subsection{Type checker}

We used the provided code for type checking.

Source code:

%\newpage
%include Typing.lhs

%\newpage
\subsection{Main program}
Our main program reads from a text file a string, this is sent to the parser to 
be tokenized and converted to a term.  This term is type checked to see if the 
entire program can be interpreted.  Then the term is sent to the small step 
evaluation process, following this the natural semantics code is called.  The 
structural operation semantics and the natural semantics produced the same 
output in all test cases. 

Source code:

\begin{code}
import System.Environment
import Data.Char
import qualified Typing as T
import qualified AbstractSyntax as S
import qualified StructuralOperationalSemantics as O
import qualified NaturalSemantics as N
--import qualified ReductionSemantics as R
import qualified CCMachine as C
import qualified SCCMachine as D
import qualified CKMachine as K
import qualified CEKMachine as L

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
  --putStrLn "---Reduction Semantics - Normal form:---"
  --let newTerm3 = R.textualMachineEval term
  --putStrLn $ show newTerm3
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
\end{code}

\subsection{Structural operational semantics (written exercise)}

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

\end{verbatim}

\subsection{Natural semantics (written exercise)}
Grammar for the natural semantics is the same as the structural operational 
semantics.
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
  
\end{verbatim}

\subsection{Natural semantics}
The natural semantics is very similar to the structural operational semantics 
but instead of using single step evaluation it uses big step evaluation which 
allows for terms to be reduced without returning the program to the root of the 
evaluation tree.  Effectively natural semantics allow for evaluation to occur 
nearby to where the most work has been done.  We implemented this code for 
Natural Semantics.

Source code:
%\newpage
%include NaturalSemantics.lhs

\end{document}


