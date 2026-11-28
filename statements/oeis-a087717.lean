import Mathlib

/-!
# A087717: iterate x ↦ 2x-1 (x noncomposite) or largest proper divisor (x composite).

Source: https://oeis.org/A087717
Credit: @Solfanbtc

A322982 is the map `g(x) = 2x - 1` if `x` is noncomposite (`1` or prime), and otherwise
`g(x) = A032742(x)`, the largest proper divisor of `x`, which is `x / minFac x`. A087717(n) is
the smallest value of the cycle (or the fixed point) that the iteration of `g` from `n`
reaches, or `0` if it never becomes periodic.

Conjecture (entry): for `n > 1`, the iteration always leads to the 3-cycle `{3, 5, 9}` or to
the 6-cycle `{19, 37, 73, 145, 29, 57}`. Since entering either cycle means passing through its
smallest element, and reaching `3` (resp. `19`) means entering that cycle, this says that for
every `n ≥ 2` some iterate `g^[k] n` equals `3` or `19`. (Verified in the entry for
`n ≤ 10^6`. Checked with python3: the definition reproduces the listed terms, and every
`2 ≤ n ≤ 200000` ends in one of the two cycles.)
-/

namespace OMA.S_oeis_a087717

/-- A322982: `2x - 1` for `x` noncomposite, else the largest proper divisor of `x`. -/
def g (x : ℕ) : ℕ := if x ≤ 1 ∨ x.Prime then 2 * x - 1 else x / x.minFac

/-- The conjecture: from every `n ≥ 2` the iteration reaches `3` or `19`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, g^[k] n = 3 ∨ g^[k] n = 19 := by
  sorry

end OMA.S_oeis_a087717
