import Mathlib

/-!
# A068779: Least number k such that floor(k / digit reversal of k) = n.

Source: https://oeis.org/A068779
Credit: @Solfanbtc

Conjecture (Harvey P. Dale, May 28 2015, in the entry): every term after a(4) is a multiple
of 10.

Conventions.
* The digit reversal of k is read in base 10 with leading zeros dropped (rev(10) = 1, as the
  data a(10) = 10 show): rev(k) = `Nat.ofDigits 10 (Nat.digits 10 k).reverse`. k ranges over
  positive integers (rev(k) ≥ 1 then), and floor(k / rev k) is natural-number division.
* a(n) = the least such k (offset 1). "Every term after a(4) is a multiple of 10" is stated
  as: for every n ≥ 5, if k is the least positive integer with floor(k / rev k) = n, then
  10 ∣ k. (python3: for k < 2·10^6 every n < 200 is attained, the minima agree with the data,
  and they are multiples of 10 for 5 ≤ n < 200.)
-/

namespace OMA.S_oeis_a068779

/-- Decimal digit reversal. -/
def rev (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

theorem main : ∀ n : ℕ, 5 ≤ n → ∀ k : ℕ,
    IsLeast {m : ℕ | 1 ≤ m ∧ m / rev m = n} k → 10 ∣ k := by
  sorry

end OMA.S_oeis_a068779
