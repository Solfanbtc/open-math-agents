import Mathlib

/-!
# A068696: Number of primes that are a concatenation nk of n and k for values of k from 1 to n.

Source: https://oeis.org/A068696
Credit: @Solfanbtc

`a(n)` (offset 1) counts the `k` with `1 ≤ k ≤ n` such that the decimal concatenation of `n`
and `k`, i.e. `n * 10^(number of digits of k) + k`, is prime. Example from the entry:
`a(20) = 2` (2011 and 2017; 2003 does not count, since `k = 3` gives 203).
The definition reproduces every term of %S, %T, %U (n = 1..98).

Conjecture (%C): `a(2)` is the only 0 in this sequence, i.e. `a(2) = 0` and `a(n) ≠ 0` for
every `n ≥ 1` with `n ≠ 2`. (Checked numerically for `n < 3000`.)
-/

namespace OMA.S_oeis_a068696

/-- Decimal concatenation of `n` and `k`. -/
def concat (n k : ℕ) : ℕ := n * 10 ^ (Nat.digits 10 k).length + k

/-- A068696: number of `k ∈ [1, n]` with `concat n k` prime. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => (concat n k).Prime)).card

theorem main : a 2 = 0 ∧ ∀ n : ℕ, 1 ≤ n → a n = 0 → n = 2 := by
  sorry

end OMA.S_oeis_a068696
