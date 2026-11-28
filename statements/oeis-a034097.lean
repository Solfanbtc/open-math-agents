import Mathlib

/-!
# A034097: Fractional part of square root of a(n) starts with digit 1

Source: https://oeis.org/A034097
Credit: @Solfanbtc

`n` is a term iff the fractional part of `√n` starts with the decimal digit `1`, i.e.
`1/10 ≤ frac(√n) < 2/10` (equivalently, Robert Israel: `m^2 + m/5 < n ≤ m^2 + 2m/5` for some
positive integer `m`); terms: `10, 17, 27, 38, 51, 66, 67, 83, 84, …` (the definition
below reproduces all 53 data terms).

Conjecture (Dimitri Papadopoulos, Oct 28 2016, OEIS formula): for any term `a(n)`, with
`k = ⌊√a(n)⌋`, `a(n)` belongs to a run of `round(1/25 + k/5)` consecutive terms that differ by one;
e.g. `k = 18` for `330`, `round(1/25 + 18/5) = 4`, and `330` lies in the run `328, 329, 330, 331`.
A "run" is the maximal block of consecutive integers, all terms, containing `a(n)`. (`1/25 + k/5`
is never a half-integer, so the rounding convention does not matter; Mathlib's `round` is used.)
Python: holds for every term below `200000`.
-/

namespace OMA.S_oeis_a034097

/-- `n` is a term of A034097: the fractional part of `√n` lies in `[1/10, 2/10)`. -/
def InA (n : ℕ) : Prop :=
  1 / 10 ≤ Int.fract (Real.sqrt n) ∧ Int.fract (Real.sqrt n) < 2 / 10

/-- Papadopoulos' conjecture: the maximal run of consecutive terms through a term `n` has length
`round(1/25 + ⌊√n⌋/5)`. -/
theorem main : ∀ n : ℕ, InA n → ∃ lo hi : ℕ, lo ≤ n ∧ n ≤ hi ∧
    (∀ m : ℕ, lo ≤ m → m ≤ hi → InA m) ∧ ¬ InA (lo - 1) ∧ ¬ InA (hi + 1) ∧
    ((hi + 1 - lo : ℕ) : ℤ) = round ((1 : ℚ) / 25 + (Nat.sqrt n : ℚ) / 5) := by
  sorry

end OMA.S_oeis_a034097
