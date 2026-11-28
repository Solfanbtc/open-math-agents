import Mathlib

/-!
# A090786: Least nonnegative integer k such that n! + n + k + 1 is prime.

Source: https://oeis.org/A090786
Credit: @Solfanbtc

`a(n)` (offset 0) is the least `k ≥ 0` with `n! + n + k + 1` prime. Examples: `a(5) = 1` (127 is
prime), `a(7) = 3` (5051).

Conjectures (F. Magata, 2004, in the entry):
1. `a(n) + n + 1` (= A037153(n), the least `m > 1` with `n! + m` prime) is prime for all
   `n > 2`;
2. `b(n) = a(0) + a(1) + ⋯ + a(n)` grows at most quadratically: `b(n) = O(n^2)`.
`main` states both. (Upstream and `statements/` contain the primorial analogues, Fortune's
conjecture and the lesser Fortunate numbers, but not these factorial versions.)
-/

namespace OMA.S_oeis_a090786

open Filter Asymptotics

/-- `a n`: the least `k ≥ 0` with `n! + n + k + 1` prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | (n.factorial + n + k + 1).Prime}

theorem main :
    (∀ n : ℕ, 2 < n → (a n + n + 1).Prime) ∧
      (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (a k : ℝ))) =O[atTop] fun n => (n : ℝ) ^ 2 := by
  sorry

end OMA.S_oeis_a090786
