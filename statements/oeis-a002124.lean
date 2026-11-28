import Mathlib

/-!
# A002124: Number of compositions of n into a sum of odd primes.

Source: https://oeis.org/A002124
Credit: @Solfanbtc

The entry says: "The g.f. -(z-1)*(z+1)*(z**2+z+1)*(z**2-z+1)/(1-z**6-z**3-z**5-z**7+z**9)
conjectured by Simon Plouffe in his 1992 dissertation is wrong." This is a settled (refuted)
conjecture; we state the entry's claim that it is wrong.

Conventions.
* `a n` is the number of compositions (ordered sums) of `n` into odd primes, with offset 0 and
  `a 0 = 1` (the empty composition), as in the entry's formula (MacMahon):
  `a(0)=1, a(1)=a(2)=0`, and `a(n) = Σ_{primes 3 ≤ p ≤ n} a(n-p)` for `n ≥ 3`. The recursion
  below gives exactly this (for n = 1, 2 the sum is empty); it reproduces the data
  1,0,0,1,0,1,1,1,2,1,3,4,3,7,7,8,14,15,21,28,33,47,58,76,103,125,...
* The numerator `-(z-1)(z+1)(z^2+z+1)(z^2-z+1)` equals `1 - z^6`. Since the denominator
  `1 - z^3 - z^5 - z^6 - z^7 + z^9` has constant term 1 (a unit in `ℤ⟦z⟧`), Plouffe's g.f.
  equals `Σ a(n) z^n` iff `(Σ a(n) z^n) * (1 - z^3 - z^5 - z^6 - z^7 + z^9) = 1 - z^6`.
  The statement says this identity fails. (Checked numerically: the conjectured g.f. gives 126
  at n = 25, while a(25) = 125.)
-/

namespace OMA.S_oeis_a002124

/-- Number of compositions of `n` into odd primes (`a 0 = 1`). -/
def a : ℕ → ℕ
  | n => (if n = 0 then 1 else 0) +
      ∑ p : Fin n, (if (p.val + 1).Prime ∧ p.val + 1 ≠ 2 then a (n - (p.val + 1)) else 0)
decreasing_by omega

theorem main :
    (PowerSeries.mk fun n => (a n : ℤ)) *
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ 3 - PowerSeries.X ^ 5 - PowerSeries.X ^ 6
        - PowerSeries.X ^ 7 + PowerSeries.X ^ 9) ≠
      1 - (PowerSeries.X : PowerSeries ℤ) ^ 6 := by
  sorry

end OMA.S_oeis_a002124
