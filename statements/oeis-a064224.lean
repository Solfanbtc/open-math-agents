import Mathlib

/-!
# A064224: Numbers having more than one representation as a product of consecutive integers > 1.

Source: https://oeis.org/A064224
Credit: @Solfanbtc

From the entry (T. D. Noe, Jul 29 2009): MacLeod and Barrodale prove that the equation
x(x+1)...(x+m-1) = y(y+1)...(y+n-1) has no solutions x > 1 and y > 1 for several pairs (m, n)
and "conjecture that (2,k) has no solution for k>3". Stated: for every k > 3 there are no
integers x, y > 1 with x(x+1) = y(y+1)...(y+k-1).

Conventions.
* (m, n) = (2, k): a product of 2 consecutive integers equal to a product of k consecutive
  integers, all factors > 1 (x > 1, y > 1). The product y(y+1)...(y+k-1) is
  `∏ i ∈ Finset.range k, (y + i)`.
* For k = 3 there are solutions (e.g. 14·15 = 5·6·7 = 210), hence "k > 3".
-/

namespace OMA.S_oeis_a064224

theorem main : ∀ k : ℕ, 3 < k → ∀ x y : ℕ, 1 < x → 1 < y →
    x * (x + 1) ≠ ∏ i ∈ Finset.range k, (y + i) := by
  sorry

end OMA.S_oeis_a064224
