import Mathlib

/-!
# A124380: O.g.f.: A(x) = Sum_{n>=0} x^n*Product_{k=0..n} (1 + k*x).

Source: https://oeis.org/A124380
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Sep 18 2024): log(a(n)) ~ n*log(n)/2 - n*(1 + log(2))/2.

Definitions.
* a(n) (offset 0) is the coefficient of x^n in Sum_{m>=0} x^m Prod_{k=0..m} (1 + k x); only
  the terms m ≤ n contribute, so a(n) is the x^n-coefficient of the polynomial
  Sum_{m=0..n} x^m Prod_{k=0..m} (1 + k x). The data 1, 1, 2, 4, 9, 22, 57, ... are reproduced
  (`#eval` of the equivalent formula a(n) = Sum_m e_(n-m)(1, ..., m), elementary symmetric
  functions, in a scratch file).
* "~": the ratio of log a(n) to n log n / 2 - n (1 + log 2)/2 tends to 1.
-/

namespace OMA.S_oeis_a124380

open Polynomial

/-- A124380(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ m ∈ Finset.range (n + 1), X ^ m * ∏ k ∈ Finset.range (m + 1), (1 + (k : ℕ[X]) * X)).coeff n

theorem main :
    Filter.Tendsto
      (fun n : ℕ => Real.log (a n) /
        ((n : ℝ) * Real.log n / 2 - (n : ℝ) * (1 + Real.log 2) / 2))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a124380
