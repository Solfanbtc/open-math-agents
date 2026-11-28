import Mathlib

/-!
# A081169: Triangle in which n-th row gives trajectory of n (including n itself) under the map x -> x/2 if x is even, x -> 3*x-1 if x is odd, stopping when reaching 1, 5 or 17.

Source: https://oeis.org/A081169
Credit: @Solfanbtc

Conjecture (in the %C line): the trajectory of every `n ≥ 1` under `x ↦ x/2` (`x` even),
`x ↦ 3x - 1` (`x` odd) always ends in one of the three loops
`1, 2, 1, …`; `5, 14, 7, 20, 10, 5, …`; `17, 50, 25, 74, 37, 110, 55, 164, 82, 41, 122, 61, 182,
91, 272, 136, 68, 34, 17, …`.

Formalization: the map `f` is on positive integers (for odd `x ≥ 1`, `3x - 1 ≥ 2` is exact in `ℕ`).
Since `1`, `5` and `17` lie on these three cycles and each cycle contains one of them, "the
trajectory ends in one of the three loops" is equivalent to "some iterate `f^[k] n` is `1`, `5` or
`17`" (which is also when the rows of the triangle stop). Stated for every `n ≥ 1` (offset 1).
Checked numerically for all `n ≤ 200000`.
-/

namespace OMA.S_oeis_a081169

/-- The map `x ↦ x/2` if `x` is even, `x ↦ 3x - 1` if `x` is odd. -/
def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x - 1

/-- Every trajectory reaches one of the three loops, i.e. reaches `1`, `5` or `17`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, f^[k] n ∈ ({1, 5, 17} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a081169
