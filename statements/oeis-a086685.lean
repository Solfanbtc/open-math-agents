import Mathlib

/-!
# A086685: Number of 1 <= i < n such that i*n+1 is prime.

Source: https://oeis.org/A086685
Credit: @Solfanbtc

`a(n) = #{i : 1 ≤ i < n, i·n + 1 prime}`, equivalently the number of primes `p < n^2` with
`p ≡ 1 (mod n)` (for `n ≥ 2`): 0, 1, 1, 2, 1, 4, 2, 2, 3, 5, ... (offset 1).

Conjecture (Thomas Ordowski, Oct 21 2014, "the standard conjecture here"):
`a(n) ~ n^2 / (2 φ(n) log n)`, `φ` Euler's totient.

Sanity check (python): the definition gives all 58 listed terms; the ratio of `a(n)` to
`n^2/(2 φ(n) log n)` is 1.11, 1.04, 1.08, 1.05, 1.07 at `n = 100, 500, 1000, 2000, 3000`.
-/

namespace OMA.S_oeis_a086685

open Filter Asymptotics

/-- A086685. -/
def a (n : ℕ) : ℕ := ((Finset.Ico 1 n).filter (fun i => (i * n + 1).Prime)).card

/-- Ordowski's conjecture: `a(n) ~ n^2 / (2 φ(n) log n)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ 2 / (2 * (Nat.totient n : ℝ) * Real.log n) := by
  sorry

end OMA.S_oeis_a086685
