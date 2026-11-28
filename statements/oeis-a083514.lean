import Mathlib

/-!
# A083514: Number of steps for iteration of map x -> (4/3)*ceiling(x) to reach an integer > 3n+1 when started at 3n+1, or -1 if no such integer is ever reached.

Source: https://oeis.org/A083514
Credit: @Solfanbtc

The map is `f x = (4/3) ⌈x⌉` on `ℚ`. Since `f x > x`, every iterate after at least one step
exceeds the starting value, so "reach an integer `> 3n+1`" means: some iterate `f^[k] (3n+1)` with
`k ≥ 1` is an integer. For example `n = 0`: 1 → 4/3 → 8/3 → 4, so `a(0) = 3`. Checked with
python3 (exact rationals): this reproduces the data 3, 2, 8, 7, 2, 3, 5, ..., and an integer is
reached for every `n < 20000` (at most 28 steps).

Conjecture (in the entry; cf. J. C. Lagarias and N. J. A. Sloane, Approximate squaring,
Experiment. Math. 13 (2004) 113-128): an integer is always reached, i.e. `a(n) ≠ -1` for all
`n ≥ 0`. `main` states this.
-/

namespace OMA.S_oeis_a083514

/-- The map `x ↦ (4/3) ⌈x⌉`. -/
def f (x : ℚ) : ℚ := 4 / 3 * (⌈x⌉ : ℚ)

theorem main :
    ∀ n : ℕ, ∃ k : ℕ, 1 ≤ k ∧ ∃ m : ℤ, f^[k] (3 * (n : ℚ) + 1) = m := by
  sorry

end OMA.S_oeis_a083514
