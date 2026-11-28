import Mathlib

/-!
# A014120: Smallest number of persistence n over product-of-nonzero-digits function.

Source: https://oeis.org/A014120
Credit: @Solfanbtc

Conjecture (comment in the entry, Marc Lapierre, 2020/2025): "It seems a safe conjecture that
this sequence is infinite."

Conventions.
* The map is the product of the nonzero decimal digits (OEIS A051801): `x ↦ ∏ d`, over the
  nonzero digits `d` of `x`. The persistence of `x` is the number of applications needed to reach
  a single digit (a number `< 10`). This matches the data: `a(0) = 0`, `a(1) = 10` (10 → 1),
  `a(2) = 25` (25 → 10 → 1), `a(3) = 39` (39 → 27 → 14 → 4), `a(4) = 77`, `a(5) = 679`,
  `a(6) = 6788`, `a(7) = 68889`, checked with `#eval` as the least numbers of these persistences.
* `a(n)` is the least number of persistence `n`, so the sequence is infinite exactly when every
  `n` is the persistence of some number (if a number has persistence `n + 1`, its image has
  persistence `n`, so the persistences that occur form an initial segment of ℕ). The statement
  is therefore: every natural number `n` is the persistence of some natural number.
-/

namespace OMA.S_oeis_a014120

/-- Product of the nonzero decimal digits of `x` (A051801). -/
def nzDigitProd (x : ℕ) : ℕ := ((Nat.digits 10 x).filter (· ≠ 0)).prod

/-- `x` has persistence `n`: `n` applications of `nzDigitProd` reach a single digit, and fewer
do not. -/
def HasPersistence (x n : ℕ) : Prop :=
  nzDigitProd^[n] x < 10 ∧ ∀ k < n, 10 ≤ nzDigitProd^[k] x

theorem main : ∀ n : ℕ, ∃ x : ℕ, HasPersistence x n := by
  sorry

end OMA.S_oeis_a014120
