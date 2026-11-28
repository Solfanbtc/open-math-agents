import Mathlib

/-!
# A086844: odd m whose iterates b(k) = floor((1 + √3) b(k-1)) are all odd

Source: https://oeis.org/A086844
Credit: @Solfanbtc

A086844: odd numbers `m` such that the sequence `b(1) = m`, `b(k) = ⌊(1 + √3) b(k-1)⌋` contains only
odd numbers: `5, 7, 13, 19, 21, 27, …` (e.g. `5, 13, 35, 95, 259, …`).

Conjecture (Benoit Cloitre, Aug 10 2003, OEIS comment): let `r(z) = (z + √(z^2 + 4z))/2` for any
integral `z ≥ 1` (`r(2) = 1 + √3`). Then the sequence `a(n) - 4n`, where `a(n)` is the sequence of
odd numbers `m` such that the sequence `b(1) = m`, `b(k) = ⌊r(z) b(k-1)⌋` contains only odd numbers,
becomes ultimately periodic. Stated for every integer `z ≥ 1`, with `a_z(n)` the `n`-th such `m`
(offset 1): there are `N` and `p > 0` with `a_z(n+p) - 4(n+p) = a_z(n) - 4n` for all `n ≥ N`.
(Python, testing 80 iterates: the `z = 2` terms are the A086844 data, and for `z = 1, …, 4`,
`a_z(n) - 4n` stays bounded and looks periodic for `m < 4000`.)
-/

namespace OMA.S_oeis_a086844

/-- `r(z) = (z + √(z^2 + 4z))/2`. -/
noncomputable def r (z : ℕ) : ℝ := (z + Real.sqrt ((z : ℝ) ^ 2 + 4 * z)) / 2

/-- The iterates `b(1) = m`, `b(k+1) = ⌊r(z) b(k)⌋` (0-indexed). -/
noncomputable def b (z m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => ⌊r z * (b z m k : ℝ)⌋₊

/-- `m` is odd and all its iterates are odd. -/
def IsTerm (z m : ℕ) : Prop := ∀ k : ℕ, Odd (b z m k)

/-- `a_z(n)`, the `n`-th such `m` (offset 1). -/
noncomputable def a (z n : ℕ) : ℕ := Nat.nth (IsTerm z) (n - 1)

/-- Cloitre's conjecture: `a_z(n) - 4n` is ultimately periodic, for every integer `z ≥ 1`. -/
theorem main : ∀ z : ℕ, 1 ≤ z → ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
    (a z (n + p) : ℤ) - 4 * (n + p) = (a z n : ℤ) - 4 * n := by
  sorry

end OMA.S_oeis_a086844
