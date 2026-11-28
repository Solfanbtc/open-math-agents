import Mathlib

/-!
# A083214: Numbers k for which 3 divides the partition number p(k)

Source: https://oeis.org/A083214
Credit: @Solfanbtc

Numbers `k ≥ 1` with `3 ∣ p(k)`, `p` the partition function (A000041): `3, 7, 9, 10, 14, 16, …`
(this reproduces all 61 data terms); `a(n)` (offset 1) is the `n`-th of them.

Conjecture (Benoit Cloitre, Oct 06 2005, OEIS formula): `a(n) = 3n + o(n)`. Stated as
`a(n) - 3n = o(n)` (`Asymptotics.IsLittleO`). (This says the `k` with `3 ∣ p(k)` have natural
density `1/3`.)
-/

namespace OMA.S_oeis_a083214

/-- `k` is a term: `k ≥ 1` and `3 ∣ p(k)`. -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ 3 ∣ Fintype.card (Nat.Partition k)

/-- A083214 (offset 1): the `n`-th term. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Cloitre's conjecture: `a(n) = 3n + o(n)`. -/
theorem main : (fun n : ℕ => (a n : ℝ) - 3 * n) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

end OMA.S_oeis_a083214
