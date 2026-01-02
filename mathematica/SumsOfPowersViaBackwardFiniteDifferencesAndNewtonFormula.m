(* ::Package:: *)

BeginPackage["SumsOfPowersViaBackwardFiniteDifferencesAndNewtonFormula`"]

(*BEGIN: Definitions *)
BackwardDifference::usage=""
MultifoldSumOfPowersRecurrence::usage=""
OrdinarySumsOfPowersViaBackwardDifferences::usage=""
ValidateOrdinarySumsOfPowersViaBackwardDifferences::usage=""

(*END: Definitions *)
(* =========================================================================DOCS END=================================================================== *)

(*BEGIN: Define 0^x = 1 for all x *)
Begin["`Private`"]
Unprotect[Power];
Power[0|0., 0|0.] = 1;
Protect[Power];
(*END: Define 0^x = 1 for all x *)

(* =========================================================================FUNCTIONS BEGIN=========================================================== *)
(*BEGIN: Definitions *)
BackwardDifference[t_, m_, j_] := Sum[(-1)^k * Binomial[j, k] * (t-k)^m, {k, 0, m}];
MultifoldSumOfPowersRecurrence[r_, n_, m_]:= 0;
MultifoldSumOfPowersRecurrence[r_, n_, m_]:= n^m /; r==0;
MultifoldSumOfPowersRecurrence[r_, n_, m_]:= Sum[MultifoldSumOfPowersRecurrence[r-1, k, m], {k, 1, n}] /; r>0;
OrdinarySumsOfPowersViaBackwardDifferences[n_, m_, t_] := Sum[BackwardDifference[t, m, j] * ((-1)^j * Binomial[t, j+1] + Binomial[j-t+n, j+1]), {j, 0, m}];
ValidateOrdinarySumsOfPowersViaBackwardDifferences[max_]:=Table[MultifoldSumOfPowersRecurrence[1, n, m] - OrdinarySumsOfPowersViaBackwardDifferences[n, m, t], {n, 0, max}, {m, 0, max}, {t, 0, max}]//Flatten
(*END: Definitions *)
End[ ]
EndPackage[ ]






