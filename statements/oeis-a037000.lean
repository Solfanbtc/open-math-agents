import Mathlib

/-!
# A037000: the n-th position of the digit 1 in the decimal expansion of π is ~ 10n

Source: https://oeis.org/A037000
Credit: @Solfanbtc

A037000 (offset 1): the positions of the digit `1` in the decimal expansion of π, where (M. F.
Hasler, in the entry) "positions" are the indices `n` of the digits `d(n)` with
`π = Sum_{n >= 0} d(n)/10^n` (so `d(0) = 3`, `d(1) = 1`). Data 1, 3, 37, 40, 49, 68, 94, …

Conjecture (in the entry): `a(n) ~ 10n`.

This is the statement that the digit 1 has asymptotic frequency 1/10 among the decimal digits of
π; it is implied by, and much weaker than, the normality of π in base 10 (stated upstream as
`pi_normal_base_ten`). Definitions: `d(n) = floor(π · 10^n) mod 10`, and `a(n)` is the `n`-th
(from 1) index `m` with `d(m) = 1` (`Nat.nth`, which is `0` if there are fewer than `n` such
indices; then the ratio would be `0`, so `main` also asserts that there are infinitely many).
-/

namespace OMA.S_oeis_a037000

/-- The `n`-th decimal digit of π (`d 0 = 3`). -/
noncomputable def d (n : ℕ) : ℕ := ⌊Real.pi * 10 ^ n⌋₊ % 10

/-- A037000: the `n`-th position of the digit `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => d m = 1) (n - 1)

open Filter Topology in
/-- The conjecture: `a(n) ~ 10n`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / (10 * n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a037000
