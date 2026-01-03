(* ::Package:: *)

BeginPackage["SumsOfPowersViaBackwardFiniteDifferencesAndNewtonFormula`"]

(*BEGIN: Definitions *)
BackwardDifference::usage=""
MultifoldSumOfPowersRecurrence::usage=""
OrdinarySumsOfPowersViaBackwardDifferences::usage=""
ValidateOrdinarySumsOfPowersViaBackwardDifferences::usage=""
EulerianNumber::usage=""
BackwardDifferencesInEulerianNumbers::usage=""
ValidateBackwardDifferencesInEulerianNumbers::usage=""
BackwardDifferencesInStirlingNumbers::usage=""
ValidateBackwardDifferencesInStirlingNumbers::usage=""
OrdinarySumsOfPowersInEulerianNumbers::usage=""
ValidateOrdinarySumsOfPowersInEulerianNumbers::usage=""
OrdinarySumsOfPowersInStirlingNumbers::usage=""
ValidateOrdinarySumsOfPowersInStirlingNumbers::usage=""
DoubleSumsOfPowersViaBackwardDifferences::usage=""
ValidateDoubleSumsOfPowersViaBackwardDifferences::usage=""

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
DoubleSumsOfPowersViaBackwardDifferences[n_, m_, t_] := Sum[BackwardDifference[t, m, j] * ((-1)^j * Binomial[t, j+1] * n^1 + (-1)^(j+1) * Binomial[t, j+2]*n^0 + Binomial[j-t+n+1, j+2]), {j, 0, m}];
ValidateDoubleSumsOfPowersViaBackwardDifferences[max_]:= Table[MultifoldSumOfPowersRecurrence[2, n, m]- DoubleSumsOfPowersViaBackwardDifferences[n, m, t], {n, 0, max}, {m, 0, max}, {t, 0, max}] //Flatten
OrdinarySumsOfPowersViaBackwardDifferences[n_, m_, t_] := Sum[BackwardDifference[t, m, j] * ((-1)^j * Binomial[t, j+1] + Binomial[j-t+n, j+1]), {j, 0, m}];
ValidateOrdinarySumsOfPowersViaBackwardDifferences[max_]:=Table[MultifoldSumOfPowersRecurrence[1, n, m] - OrdinarySumsOfPowersViaBackwardDifferences[n, m, t], {n, 0, max}, {m, 0, max}, {t, 0, max}]//Flatten
EulerianNumber[0, 0] = 1;
EulerianNumber[n_, k_] /; k < 0 || k >= n := 0;
EulerianNumber[n_, k_] := EulerianNumber[n, k] = (k + 1) EulerianNumber[n - 1, k] + (n - k) EulerianNumber[n - 1, k - 1];
BackwardDifferencesInEulerianNumbers[t_, m_, j_] := Sum[EulerianNumber[m, k] * Binomial[t+k-j, m-j], {k, 0, m}];
ValidateBackwardDifferencesInEulerianNumbers[max_] := Table[BackwardDifference[t, m, j]-BackwardDifferencesInEulerianNumbers[t, m, j], {m, 0, max}, {j, 0, m}, {t, 0, max}] //Flatten
OrdinarySumsOfPowersInEulerianNumbers[n_, m_, t_] := Sum[BackwardDifferencesInEulerianNumbers[t, m, j] * ((-1)^j * Binomial[t, j+1] + Binomial[j-t+n, j+1]), {j, 0, m}];
ValidateOrdinarySumsOfPowersInEulerianNumbers[max_]:=Table[MultifoldSumOfPowersRecurrence[1, n, m] - OrdinarySumsOfPowersInEulerianNumbers[n, m, t], {n, 0, max}, {m, 0, max}, {t, 0, max}]//Flatten
BackwardDifferencesInStirlingNumbers[t_, m_, j_] := Sum[StirlingS2[m,k] * Binomial[t-j, k-j] * k!, {k, j, m}];
ValidateBackwardDifferencesInStirlingNumbers[max_]:= Table[BackwardDifference[t, m, j]-BackwardDifferencesInStirlingNumbers[t, m, j], {m, 0, max}, {j, 0, m}, {t, 0, max}] //Flatten
OrdinarySumsOfPowersInStirlingNumbers[n_, m_, t_] := Sum[BackwardDifferencesInStirlingNumbers[t, m, j] * ((-1)^j * Binomial[t, j+1] + Binomial[j-t+n, j+1]), {j, 0, m}];
ValidateOrdinarySumsOfPowersInStirlingNumbers[max_]:=Table[MultifoldSumOfPowersRecurrence[1, n, m] - OrdinarySumsOfPowersInStirlingNumbers[n, m, t], {n, 0, max}, {m, 0, max}, {t, 0, max}]//Flatten
(*END: Definitions *)
End[ ]
EndPackage[ ]






