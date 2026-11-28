import Mathlib

/-!
# A072340: Steps to reach an integer from n/3 under x ↦ x ⌈x⌉

Source: https://oeis.org/A072340
Credit: @Solfanbtc

`a(n)` (offset 3) is the number of steps to reach an integer starting with `n/3` and iterating the
map `x ↦ x ⌈x⌉`, or `-1` if no integer is ever reached: `0, 2, 6, 0, 1, 1, 0, 5, …` (an exact
rational simulation reproduces all 105 data terms).

Conjecture (N. J. A. Sloane and J. C. Lagarias, OEIS comment): an integer is always reached, i.e.
for every `n ≥ 3` some iterate of `x ↦ x ⌈x⌉` started at `n/3` is an integer. (The offset matters:
for `n = 1, 2` the start `1/3`, `2/3` is a fixed point of the map, `x ⌈x⌉ = x`, so no integer is
reached.)
-/

namespace OMA.S_oeis_a072340

/-- The map `x ↦ x ⌈x⌉` on `ℚ`. -/
def f (x : ℚ) : ℚ := x * ⌈x⌉

/-- Sloane–Lagarias conjecture: starting from `n/3`, `n ≥ 3`, an integer is always reached. -/
theorem main : ∀ n : ℕ, 3 ≤ n → ∃ k : ℕ, ∃ m : ℤ, f^[k] ((n : ℚ) / 3) = m := by
  sorry

end OMA.S_oeis_a072340
