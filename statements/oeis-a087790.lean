import Mathlib

/-!
# A087790: Partial sums of A085068.

Source: https://oeis.org/A087790
Credit: @Solfanbtc

A085068(n) (`n ≥ 0`) is the number of steps `i ≥ 1` for the iteration of `x ↦ (4/3)⌈x⌉`, started
at `x = n`, to reach an integer, or `-1` if no integer is ever reached. `a(n) = Σ_{k=0}^{n}
A085068(k)` (offset `0`). This reproduces the data (Python, exact rationals).

Conjecture (Benoit Cloitre, in the entry): `a(n) = 3n + O(√n)`, i.e. `|a(n) - 3n| ≤ C √n` for
all large `n`. (Python: `(a(n) - 3n)/√n` is `0.19, -0.16, 0.61, 0.59` at `n = 10^3, 10^4, 10^5,
2·10^5`.)
-/

namespace OMA.S_oeis_a087790

/-- The map `x ↦ (4/3)⌈x⌉`. -/
def f (x : ℚ) : ℚ := 4 / 3 * ⌈x⌉

open Classical in
/-- A085068(n): the least `i ≥ 1` with `f^[i] n` an integer, or `-1` if there is none. -/
noncomputable def steps (n : ℕ) : ℤ :=
  if h : ∃ i : ℕ, 1 ≤ i ∧ (f^[i] (n : ℚ)).den = 1 then (Nat.find h : ℤ) else -1

/-- A087790. -/
noncomputable def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), steps k

theorem main : (fun n : ℕ => (a n : ℝ) - 3 * n) =O[Filter.atTop] (fun n : ℕ => Real.sqrt n) := by
  sorry

end OMA.S_oeis_a087790
