import Mathlib

/-!
# A039831: Largest coefficient in expansion of Product (1+q^1+q^3+...+q^(2i-1)), i=1 to n.

Source: https://oeis.org/A039831
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Jan 05 2023, in the entry): a(n) ~ 3 * n^n / exp(n).

Conventions.
* The i-th factor is 1 + q + q^3 + ... + q^(2i-1) = 1 + Σ_{k=1}^{i} q^(2k-1) (as in the
  entry's Mathematica program); a(n) (offset 1) is the largest coefficient of the product over
  i = 1..n. This gives 1, 2, 4, 13, 57, 315, ... (python3: all 20 listed terms).
* "~" is stated as a(n) / (3 n^n / e^n) → 1. (python3: the ratio is 0.9506 at n = 20,
  0.9707 at n = 40, 0.9792 at n = 60.)
-/

namespace OMA.S_oeis_a039831

open Polynomial

/-- The product of the factors 1 + Σ_{k=1}^{i} q^(2k-1), i = 1..n. -/
noncomputable def P (n : ℕ) : ℕ[X] :=
  ∏ i ∈ Finset.Icc 1 n, (1 + ∑ k ∈ Finset.Icc 1 i, (X : ℕ[X]) ^ (2 * k - 1))

/-- A039831: the largest coefficient of P n. -/
noncomputable def a (n : ℕ) : ℕ := (Finset.range ((P n).natDegree + 1)).sup (fun j => (P n).coeff j)

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (3 * (n : ℝ) ^ n / Real.exp n)) Filter.atTop
      (nhds 1) := by
  sorry

end OMA.S_oeis_a039831
