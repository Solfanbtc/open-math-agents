import Mathlib

/-!
# A129890: a(n) = (2*n+2)!! - (2*n+1)!!.

Source: https://oeis.org/A129890
Credit: @Solfanbtc

Conjecture (Peter Bala, Jul 06 2025, in the entry): a(n) = (2n+2) (2n+2)! *
Sum_{k >= 1} (-1)^(k+1) / Product_{j = 0..n+1} (k + 2j). (The entry adds, Dec 03 2025, that
"this identity can be verified using Maple's sum command"; no proof is referenced.)

Conventions.
* n!! is Mathlib's `Nat.doubleFactorial`; a(n) = (2n+2)!! - (2n+1)!! (offset 0), computed in ℝ
  (it is positive): 1, 5, 33, 279, 2895, ...
* The series is absolutely convergent for n ≥ 0 (its terms are O(k^-2)); it is stated with
  `HasSum`, indexing k = m + 1, m ≥ 0, and with both sides divided by the nonzero factor
  (2n+2)(2n+2)!: the series sums to a(n) / ((2n+2)(2n+2)!).
* python3 (200000 terms): the right side gives 1.0000, 5.0000, 33.000, 279.00, 2895.0, 35685.0
  for n = 0..5.
-/

namespace OMA.S_oeis_a129890

theorem main : ∀ n : ℕ,
    HasSum
      (fun m : ℕ => (-1 : ℝ) ^ (m + 2) /
        ∏ j ∈ Finset.range (n + 2), ((m + 1 : ℝ) + 2 * j))
      ((((2 * n + 2).doubleFactorial : ℝ) - ((2 * n + 1).doubleFactorial : ℝ)) /
        ((2 * n + 2 : ℝ) * ((2 * n + 2).factorial : ℝ))) := by
  sorry

end OMA.S_oeis_a129890
