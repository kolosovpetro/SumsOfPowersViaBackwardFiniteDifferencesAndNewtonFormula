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
MultifoldSumsOfPowersViaBackwardDifference::usage=""
MultifoldSumsOfPowersViaBackwardDifferenceBinomialForm::usage=""
ValidateMultifoldSumsOfPowersViaBackwardDifference::usage=""
ValidateMultifoldSumsOfPowersBackwardDiffBinomialForm::usage=""
OrdinaryStirlingSumsOfPowersInZero::usage=""
ValidateOrdinaryStirlingSumsOfPowersInZero::usage=""
OrdinaryStirlingSumsOfPowersInZeroAltered::usage=""
ValidateOrdinaryStirlingSumsOfPowersInZeroAltered::usage=""
MultifoldSumsOfPowersBinomialFormShifted::usage=""
ValidateMultifoldSumsOfPowersBinomialFormShifted::usage=""
MultifoldSumsOfPowersInStirlingNumbers::usage=""
ValidateMultifoldSumsOfPowersInStirlingNumbers::usage=""
MultifoldSumsOfPowersInEulerianNumbers::usage=""
ValidateMultifoldSumsOfPowersInEulerianNumbers::usage=""
MultifoldBinomialSumRecurrence::usage=""
MultifoldBinomialSumClosedForm::usage=""

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
MultifoldSumsOfPowersViaBackwardDifference[r_, n_, m_, t_] := Sum[BackwardDifference[t, m, j] * ( Binomial[j-t+n+r-1, j+r] + Sum[(-1)^(j+s) * Binomial[t, j+s+1] * MultifoldSumOfPowersRecurrence[r-1-s, n, 0], {s, 0, r-1}] ), {j, 0, m}];
ValidateMultifoldSumsOfPowersViaBackwardDifference[max_] := Table[MultifoldSumOfPowersRecurrence[r, n, m]- MultifoldSumsOfPowersViaBackwardDifference[r, n, m, t], {r, 0, max}, {n, 0, max}, {m, 0, max}, {t, 0, max}] //Flatten;
MultifoldSumsOfPowersViaBackwardDifferenceBinomialForm[r_, n_, m_, t_] := Sum[BackwardDifference[t, m, j] * ( Binomial[j-t+n+r-1, j+r] + Sum[(-1)^(j+s) * Binomial[t, j+s+1] * Binomial[r-s+n-2, r-s-1], {s, 0, r-1}] ), {j, 0, m}];
ValidateMultifoldSumsOfPowersBackwardDiffBinomialForm[max_] := Table[MultifoldSumOfPowersRecurrence[r, n, m]- MultifoldSumsOfPowersViaBackwardDifferenceBinomialForm[r, n, m, t], {r, 0, max}, {n, 0, max}, {m, 0, max}, {t, 0, max}] //Flatten;
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
OrdinaryStirlingSumsOfPowersInZero[n_, m_] := Sum[Sum[Binomial[j+n, j+1] * Binomial[-j, k-j] * StirlingS2[m, k] * k!, {k, j, m}], {j, 0, m}];
ValidateOrdinaryStirlingSumsOfPowersInZero[max_]:= Table[MultifoldSumOfPowersRecurrence[1, n, m] - OrdinaryStirlingSumsOfPowersInZero[n, m], {n, 0, max}, {m, 0, max}] //Flatten
OrdinaryStirlingSumsOfPowersInZeroAltered[n_, m_] := Sum[Sum[(-1)^(k-j) * Binomial[k-1, j-1] * Binomial[j+n, j+1] * StirlingS2[m,k] * k!, {k, j, m}], {j, 0, m}];
ValidateOrdinaryStirlingSumsOfPowersInZeroAltered[max_]:= Table[MultifoldSumOfPowersRecurrence[1, n, m] - OrdinaryStirlingSumsOfPowersInZeroAltered[n, m], {n, 0, max}, {m, 0, max}] //Flatten
MultifoldSumsOfPowersBinomialFormShifted[r_, n_, m_, t_] := Sum[BackwardDifference[t, m, j] * ( Binomial[j-t+n+r, j+r+1] + Sum[(-1)^(j+s) * Binomial[t, j+s+1] * Binomial[r-s+n-1, r-s], {s, 0 , r}] ), {j, 0, m}];
ValidateMultifoldSumsOfPowersBinomialFormShifted[max_]:= Table[MultifoldSumOfPowersRecurrence[r+1, n, m]- MultifoldSumsOfPowersBinomialFormShifted[r, n, m, t], {r, 0, max}, {n, 0, max}, {m, 0, max}, {t, 0, max}]//Flatten
MultifoldSumsOfPowersInStirlingNumbers[r_, n_, m_, t_] := Sum[Sum[ ( Binomial[j-t+n+r, j+r+1] + Sum[(-1)^(j+s) * Binomial[t, j+s+1] * Binomial[r-s+n-1, r-s], {s, 0, r}] ) * Binomial[t-j, k-j] * StirlingS2[m, k] * k!, {k, j, m}], {j, 0, m}];
ValidateMultifoldSumsOfPowersInStirlingNumbers[max_]:= Table[MultifoldSumOfPowersRecurrence[r+1, n, m]- MultifoldSumsOfPowersInStirlingNumbers[r, n, m, t], {r, 0, max}, {n, 0, max}, {m, 0, max}, {t, 0, max}] //Flatten
MultifoldSumsOfPowersInEulerianNumbers[r_, n_, m_, t_] := Sum[Sum[ ( Binomial[j-t+n+r, j+r+1] + Sum[(-1)^(j+s) * Binomial[t, j+s+1] * Binomial[r-s+n-1, r-s], {s, 0, r}]) * Binomial[t+k-j, m-j] * EulerianNumber[m, k], {k, 0, m}], {j, 0, m}];
ValidateMultifoldSumsOfPowersInEulerianNumbers[max_] := Table[MultifoldSumOfPowersRecurrence[r+1, n, m]- MultifoldSumsOfPowersInEulerianNumbers[r, n, m, t], {r, 0, max}, {n, 0, max}, {m, 0, max}, {t, 0, max}] //Flatten
(* Base cases *)
MultifoldBinomialSumRecurrence[r_, n_, t_, j_] := 0;
MultifoldBinomialSumRecurrence[r_, n_, t_, j_] := Binomial[n - t + j - 1, j] /; r == 0;
MultifoldBinomialSumRecurrence[r_, n_, t_, j_] := Sum[MultifoldBinomialSumRecurrence[r - 1, k, t, j], {k, 1, n}]/; r > 0;

(* Closed-form multifold binomial sum *)
MultifoldBinomialSumClosedForm[r_, n_, t_, j_] :=
    Binomial[n - t + j + r - 1, j + r]
    -
    Sum[
      Binomial[j - t + (r - 1 - s), j + r - s]*
        MultifoldSumOfPowersRecurrence[s, n, 0],
      {s, 0, r - 1}
    ];

(*END: Definitions *)
End[ ]
EndPackage[ ]



