import Mathlib

/-!
# A092671: Numbers n such that there exists a solution to the equation 1 = 1/x1 + ... + 1/xk (for any k), 0 < x1 < ... < xk = n.

Source: https://oeis.org/A092671
Credit: @Solfanbtc

Conjecture (Jon E. Schoenfield, Apr 06 2014, verified through n = 2*10^5, OEIS A092671): for any
n > 1, let P be the largest divisor of n that is either a prime p or a prime power p^e (e > 1),
and let m = n/P. Then n is in the sequence iff p is a factor of the numerator of a sum
1/m + 1/x_1 + ... + 1/x_i, where x_1, ..., x_i are distinct integers < m.

Conventions.
* Membership (`InA092671`): some finite set S of positive integers <= n containing n has
  Σ_{x ∈ S} 1/x = 1 (the x_j are distinct, the largest is x_k = n). This is the set `Erdos292.A`
  of FormalConjectures; the characterization below is not stated there.
* P is the largest prime power dividing n (`IsPrimePow` covers p and p^e), and p = P.minFac.
* The x_j are distinct positive integers < m, i.e. a finite subset X of {1, ..., m - 1}
  (possibly empty); the sum is a rational number and "numerator" is that of its reduced form
  (`Rat.num`).
Checked numerically: for every n <= 145 (the listed range) with m <= 18 the criterion agrees with
the listed terms.
-/

namespace OMA.S_oeis_a092671

/-- `n` is the largest denominator of an Egyptian fraction representation of 1. -/
def InA092671 (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, n ∈ S ∧ (∀ x ∈ S, 0 < x ∧ x ≤ n) ∧ ∑ x ∈ S, (1 : ℚ) / x = 1

theorem main : ∀ n : ℕ, 1 < n → ∀ P : ℕ, IsGreatest {d : ℕ | d ∣ n ∧ IsPrimePow d} P →
    (InA092671 n ↔
      ∃ X : Finset ℕ, (∀ x ∈ X, 0 < x ∧ x < n / P) ∧
        ((P.minFac : ℤ) ∣ ((1 : ℚ) / ((n / P : ℕ) : ℚ) + ∑ x ∈ X, (1 : ℚ) / x).num)) := by
  sorry

end OMA.S_oeis_a092671
