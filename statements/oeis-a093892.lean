import Mathlib

/-!
# A093892: Index of first occurrence of n in A093890, or 0 if no such number exists.

Source: https://oeis.org/A093892
Credit: @Solfanbtc

A093890(n) (`n ≥ 1`) is the number of primes that arise as the sum of one or more (distinct)
divisors of `n`. For example A093890(4) = 4: the primes 2, 3 = 1 + 2, 5 = 1 + 4, 7 = 1 + 2 + 4.
Such a sum is at most `σ(n)`, so the primes counted lie in `[0, σ(n)]`. Checked with python3:
this reproduces the first 40 terms of A093890. A093892(m) is the least `n ≥ 1` with
A093890(n) = m, or 0 if there is none.

Conjecture (A. Murthy): there are infinitely many zeros in A093892, i.e. infinitely many `m` are
not a value of A093890. `main` states this.
-/

namespace OMA.S_oeis_a093892

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A093890(n): the number of primes that are sums of nonempty sets of divisors of `n`. -/
def A093890 (n : ℕ) : ℕ :=
  ((Finset.range (σ 1 n + 1)).filter
    (fun p => p.Prime ∧ ∃ S ∈ n.divisors.powerset, S.sum id = p)).card

theorem main : {m : ℕ | ∀ n : ℕ, 1 ≤ n → A093890 n ≠ m}.Infinite := by
  sorry

end OMA.S_oeis_a093892
