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

Code:
%\newpage
%include NaturalSemanticsWithEnvironmentsClosuresAndDeBruijnIndices.lhs

\subsection{3.3 CES Machine}
\label{sec:core}

Source code:
%\newpage
%include CESMachine.lhs

\subsection{3.4 Continuation Passing Style (CPS)}
\label{sec:core}

Code:
%\newpage
%include CPS.lhs

\subsection{3.5 CE3R Machine}
\label{sec:core}

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
  putStrLn ("---Evaluation of CPS using Operational Semantics:---")
  let opTerm = O.eval cpsTerm
  putStrLn $ show opTerm
  putStrLn ("---Evaluation of CPS using CE3R Small Step Semantics:---")
  let ce3rTerm = CR.eval (DB.toDeBruijn cpsTerm)
  putStrLn $ show ce3rTerm

\end{code}
\end{document}


