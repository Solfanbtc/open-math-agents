import Mathlib

/-!
# A090975: Least integer k such that n!+1-k is prime.

Source: https://oeis.org/A090975
Credit: @Solfanbtc

`a(n)` (offset `0`) is the least `k ≥ 0` with `n! + 1 - k` prime, i.e. `n! + 1 - prevprime(n! + 2)`
(the Maple program). `k ≤ n! - 1` always works, since `n! + 1 - k = 2` for `k = n! - 1`, so the
subtraction stays positive. This reproduces every term of %S, %T, %U (Python).

Conjectures (Frederick Magata, in the entry):
1. `|a(n) - 1|` is either `1` or a prime number. Stated here for all `n ≥ 0`. (Python: true for
   `0 ≤ n < 200`. For `a(n) = 0`, i.e. `n! + 1` prime, `|a(n) - 1| = 1`.)
2. The entry also asks "Is the growth of b(n) := sum(a(k),k=0..n) quadratic, that is
   b(n)=O(n^2)?". That is posed as a question, not a conjecture, so it is not stated.
-/

namespace OMA.S_oeis_a090975

/-- A090975. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | k < n.factorial + 1 ∧ (n.factorial + 1 - k).Prime}

theorem main : ∀ n : ℕ, Int.natAbs ((a n : ℤ) - 1) = 1 ∨ (Int.natAbs ((a n : ℤ) - 1)).Prime := by
  sorry

end OMA.S_oeis_a090975
