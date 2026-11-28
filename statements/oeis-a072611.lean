import Mathlib

/-!
# A072611: Numbers k such that phi(k) divides sigma(k+1) - sigma(k)

Source: https://oeis.org/A072611
Credit: @Solfanbtc

Numbers `k ≥ 1` such that `φ(k)` divides the integer `σ(k+1) - σ(k)` (which may be negative):
`1, 2, 6, 14, 30, 40, 70, 140, …` (this reproduces all 45 data terms). `a(n)` (offset 1) is the
`n`-th term.

Conjecture (Benoit Cloitre, Aug 07 2002, OEIS formula): `lim_{n→∞} log(a(n))/log(n)` exists and
equals `2.6…`. Stated as: there is `L` with decimal expansion beginning `2.6` (`2.6 ≤ L < 2.7`)
and `log(a(n))/log(n) → L`. (This implicitly asserts that the sequence is infinite.)
-/

namespace OMA.S_oeis_a072611

open ArithmeticFunction

/-- `k` is a term of A072611. -/
def IsTerm (k : ℕ) : Prop :=
  1 ≤ k ∧ (Nat.totient k : ℤ) ∣ (sigma 1 (k + 1) : ℤ) - sigma 1 k

/-- A072611 (offset 1): the `n`-th term. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Cloitre's conjecture: `log(a(n))/log(n) → 2.6…`. -/
theorem main : ∃ L : ℝ, 2.6 ≤ L ∧ L < 2.7 ∧
    Filter.Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) Filter.atTop (nhds L) := by
  sorry

end OMA.S_oeis_a072611
