import Mathlib

/-!
# A064337: Minimal prime numbers with increasing prime differences.

Source: https://oeis.org/A064337
Credit: @Solfanbtc

Conjecture (Bill McEachen, Apr 04 2024, OEIS A064337): a(n) ~ K n^2 log(n) for some constant K.

Reading: a(n) / (n^2 log n) converges to a constant K > 0 (K = 0 or K = ∞ would not be an
asymptotic equivalence; the lower bound a(n) >> n^2 log n recorded in the entry shows K > 0 is
forced). The constant is not specified in the entry, so it is existentially quantified.

Definition (from the entry): a(1) = 2, a(n+1) = the least prime p >= a(n) + prime(n). Here
`a n` is indexed from 1 (`a 0` is an unused junk value equal to 2), prime(n) is
`Nat.nth Nat.Prime (n - 1)`, and the least prime >= x is `sInf {p | p.Prime ∧ x ≤ p}`.
Checked numerically: the listed terms 2, 5, 11, 17, 29, ... are reproduced, and
a(n)/(n^2 log n) = 0.524, 0.531, 0.534, 0.535 at n = 100, 500, 1000, 1500.
-/

namespace OMA.S_oeis_a064337

open Filter

/-- The least prime `≥ x`. -/
noncomputable def nextPrime (x : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ x ≤ p}

/-- a(n), for n ≥ 1 (with `a 0 = a 1 = 2`). -/
noncomputable def a : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | n + 1 => nextPrime (a n + Nat.nth Nat.Prime (n - 1))

theorem main : ∃ K : ℝ, 0 < K ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) ^ 2 * Real.log n)) atTop (nhds K) := by
  sorry

end OMA.S_oeis_a064337
