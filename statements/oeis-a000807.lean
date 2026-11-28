import Mathlib

/-!
# A000807: Quadratic invariants.

Source: https://oeis.org/A000807
Credit: @Solfanbtc

Conjecture (Velin Yanev, OEIS A000807, formula section, Aug 29 2026):
a(n) = 2*exp(-2) * Sum_{k >= 1} k^(2*n)*BesselI(k, 2) for n > 0.

Conventions:
* The terms (offset 0: 1, 2, 14, 182, 3614, ...) are those of the e.g.f.
  exp(exp(x) + exp(-x) - 2) (Jovovic); here they are computed by the recurrence of the entry
  (Ilya Gutkovskiy): a(0) = 1, a(n) = 2 * Sum_{k=1..n} binomial(2n-1, 2k-1) * a(n-k).
  Checked in Python: it gives all 18 listed terms of %S/%T/%U.
* BesselI(k, x) is the modified Bessel function of the first kind,
  I_k(x) = Sum_{m >= 0} (x/2)^(2m+k) / (m! (m+k)!) for integer k ≥ 0, so
  I_k(2) = Sum_{m >= 0} 1 / (m! (m+k)!). Both series are written as `tsum`s (they converge
  absolutely).
* n > 0 as in the source (at n = 0 the right side is about 0.6915, not a(0) = 1). Checked
  numerically to 75 digits for 1 ≤ n ≤ 7.
-/

namespace OMA.S_oeis_a000807

/-- A000807, by Gutkovskiy's recurrence. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * ∑ k : Fin (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * a (n - k)
decreasing_by omega

/-- The modified Bessel function of the first kind at `2`: `I_k(2) = Σ_{m ≥ 0} 1/(m! (m+k)!)`. -/
noncomputable def besselITwo (k : ℕ) : ℝ :=
  ∑' m : ℕ, 1 / ((Nat.factorial m : ℝ) * (Nat.factorial (m + k) : ℝ))

/-- Yanev's conjecture: `a(n) = 2 e^{-2} Σ_{k ≥ 1} k^{2n} I_k(2)` for `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n →
    (a n : ℝ) = 2 * Real.exp (-2) * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (2 * n) * besselITwo (k + 1) := by
  sorry

end OMA.S_oeis_a000807
