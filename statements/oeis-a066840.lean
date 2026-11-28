import Mathlib

/-!
# A066840: Sum of positive integers k where k <= n/2 and gcd(k,n) = 1.

Source: https://oeis.org/A066840
Credit: @Solfanbtc

Conjecture (Thomas Ordowski, Nov 12 2014, OEIS A066840): a(n) = n phi(n)/8 + O(n).
Status: the entry records that the conjecture is true (Chai Wah Wu, Apr 10 2026, citing the
article by Baum linked from the entry); stated faithfully.

a(n) = Σ k over 1 <= k <= n/2 (i.e. k <= floor(n/2)) with gcd(k, n) = 1 (offset 1; e.g. a(8) = 1 + 3).
The error term is a big-O as n → ∞ in ℝ.
-/

namespace OMA.S_oeis_a066840

open Filter Asymptotics

/-- a(n) = Σ_{1 ≤ k ≤ n/2, gcd(k, n) = 1} k. -/
def a (n : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 (n / 2)).filter (fun k => Nat.Coprime k n), k

theorem main :
    (fun n : ℕ => (a n : ℝ) - (n : ℝ) * (Nat.totient n : ℝ) / 8) =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

end OMA.S_oeis_a066840
