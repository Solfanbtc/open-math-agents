import Mathlib

/-!
# A008366: Smallest prime factor is >= 17.

Source: https://oeis.org/A008366
Credit: @Solfanbtc

Conjecture (Gary Detlefs, Dec 27 2011, OEIS A008366, %F line): the terms n > 1 of A008366
are exactly the numbers n > 1 such that (Sum_{k=1..n} k^10) mod n = 0 and
(Sum_{k=1..n} k^12) mod n = 0.

A008366 is the set of positive integers whose smallest prime factor is >= 17 (the 17-rough
numbers, with 1 as first term). For n > 1 this means: every prime p dividing n has p ≥ 17.

Checked numerically for 2 ≤ n < 20000: no discrepancy.
-/

namespace OMA.S_oeis_a008366

theorem main : ∀ n : ℕ, 1 < n →
    ((n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 10 ∧ n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 12) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → 17 ≤ p) := by
  sorry

end OMA.S_oeis_a008366
