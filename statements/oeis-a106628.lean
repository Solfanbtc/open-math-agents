import Mathlib

/-!
# A106628: Anomalous prime numbers.

Source: https://oeis.org/A106628
Credit: @Solfanbtc

Conjecture (Charles R Greathouse IV, Aug 20 2017, %F line of A106628): `a(n) ~ n log n`.

Definition used. A prime `p` with next prime `q` is anomalous iff neither `q - 1` nor `q + 1`
is divisible by `q - p` (Greathouse's characterization in the entry, which is the definition
used by its PARI and Mathematica programs; the original description is via the extended Euclid
variant "Anomalia": `|t + d| > 1` for the coefficients with `t p + d q = 1`).

Formalization.
* `q = Nat.nth Nat.Prime (k + 1)` is the prime after `p = Nat.nth Nat.Prime k`.
* `a n = Nat.nth IsAnomalous n` is 0-indexed (OEIS offset 1); the shift `n ↦ n + 1` does not
  change `~ n log n`. The conjecture presupposes infinitely many terms; `IsEquivalent` with
  the eventually positive `n log n` already forces `a n ≠ 0` eventually, hence infinitude.
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`.

Checked with python3: the definition reproduces all listed %S/%T/%U terms (199, 211, 283, ...,
2017). (Convergence is slow: below `3 * 10^6` there are 90382 terms and `a(n)/(n log n) ≈ 2.9`.)
-/

namespace OMA.S_oeis_a106628

open Asymptotics Filter

/-- `p` is an anomalous prime: `p` is the `k`-th prime, `q` the next one, and `q - p` divides
neither `q - 1` nor `q + 1`. -/
def IsAnomalous (p : ℕ) : Prop :=
  ∃ k : ℕ, p = Nat.nth Nat.Prime k ∧
    ¬ (Nat.nth Nat.Prime (k + 1) - p ∣ Nat.nth Nat.Prime (k + 1) - 1) ∧
    ¬ (Nat.nth Nat.Prime (k + 1) - p ∣ Nat.nth Nat.Prime (k + 1) + 1)

/-- Greathouse's conjecture: the `n`-th anomalous prime is asymptotic to `n log n`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (Nat.nth IsAnomalous n : ℝ))
    (fun n : ℕ => (n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a106628
