import Mathlib

/-!
# A087707: Number of steps for iteration of map x -> (5/3)*ceiling(x) to reach an integer > n when started at n, or -1 if no such integer is ever reached.

Source: https://oeis.org/A087707
Credit: @Solfanbtc

Conjecture (OEIS A087707): an integer is always reached, i.e. for every n >= 1 (offset 1) some
iterate S^k(n) with k >= 1 of S(x) = (5/3) ceiling(x) is an integer. (Such an integer is > n:
the iterates increase, S(x) >= (5/3) x > x for x > 0.)
Checked numerically: the step counts 5, 4, 1, 3, 2, 1, 2, 3, 1, 10, ... reproduce the listed terms.
-/

namespace OMA.S_oeis_a087707

/-- S(x) = (5/3) ⌈x⌉. -/
def S (x : ℚ) : ℚ := 5 / 3 * ⌈x⌉

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ ∃ z : ℤ, S^[k] (n : ℚ) = z := by
  sorry

end OMA.S_oeis_a087707
