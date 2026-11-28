import Mathlib

/-!
# OEIS A090892: solutions of a floor equation with r = √2

Source: https://oeis.org/A090892
`a n` lists the solutions `x` of `⌊x r ⌊x / r⌋⌋ = ⌊(x / r) ⌊x r⌋⌋` with `r = √2`
(data: 0, 1, 2, 3, 6, 9, 10, 12, 13, 16, ...). The entry's formula line says: it seems that
`a(n) = 2n + o(n)`; conjecture: `a(n) = 2n + O(1)`. We state the conjecture `a(n) = 2n + O(1)`.

Conventions. Solutions are natural numbers `x`, listed in increasing order from `a 0`
(offset `0`, `a 0 = 0`); `O(1)` means `|a(n) - 2n| ≤ C` for a constant `C`.
A python3 check with 80-digit arithmetic reproduces all listed terms; for `x ≤ 20000`,
`a(n) - 2n` stays in `[-7, 3]`.

Remark (not part of the statement). By the comment in the entry, the terms `≥ 2` are the `n`
with `⌊n √2⌋` even, i.e. with `{n / √2} < 1/2`. By Kesten's theorem (1966) on bounded remainder
intervals, `1/2 ∉ ℤ + ℤ/√2` suggests the conjecture as stated is false; it is stated here
faithfully as the source gives it.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a090892

open Real

/-- `x` solves the floor equation with `r = √2`. -/
def P (x : ℕ) : Prop :=
  ⌊(x : ℝ) * √2 * ⌊(x : ℝ) / √2⌋⌋ = ⌊(x : ℝ) / √2 * ⌊(x : ℝ) * √2⌋⌋

theorem main : ∃ C : ℝ, ∀ n : ℕ, |(Nat.nth P n : ℝ) - 2 * n| ≤ C := by
  sorry

end OMA.S_oeis_a090892
