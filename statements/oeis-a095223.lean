import Mathlib

/-!
# A095223: a(n) is the least Fibonacci number such that a(n) - a(n-1) is prime; a(0)=1.

Source: https://oeis.org/A095223
Credit: @Solfanbtc

Conjecture (entry comment): The sequence is infinite.

Formalization.
* `a 0 = 1` and `a (n+1)` is the least Fibonacci number `F` with `F - a n` prime. Natural
  subtraction truncates at 0, which is not prime, so automatically `F > a n`, as in the
  definition (a(n) - a(n-1) is a prime, hence positive).
* `a (n+1)` is an `sInf`; it is meaningful as long as the set is nonempty. "The sequence is
  infinite" means that the construction never stops: at every step some Fibonacci number
  exceeds the previous term by a prime. That is the statement of `main`.
* With these definitions the first 15 terms are the data 1, 3, 5, 8, 13, 144, 233, 2584, 4181,
  46368, 75025, 14930352, 7778742049, ... (checked with python3).
-/

namespace OMA.S_oeis_a095223

/-- A095223. -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {F : ℕ | (∃ k : ℕ, Nat.fib k = F) ∧ (F - a n).Prime}

theorem main : ∀ n : ℕ, ∃ k : ℕ, (Nat.fib k - a n).Prime := by
  sorry

end OMA.S_oeis_a095223
