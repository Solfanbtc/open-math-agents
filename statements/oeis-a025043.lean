import Mathlib

/-!
# A025043: the sequence "not of the form prime + an earlier term" has finitely many even terms

Source: https://oeis.org/A025043
Credit: @Solfanbtc

A025043 (offset 1): `a(1) = 0`, and `a(n)` is the least number greater than `a(n-1)` that is not
of the form `prime + a(k)` with `k < n`. Data 0, 1, 9, 10, 25, 34, 35, 49, 55, 85, …

Conjecture (in the entry): "there are only finitely many even terms." (The entry reports that the
only even terms up to `a(10000)` are 0, 10, 34, 100, 310.)

Definition. Since primes are at least 2, a number `m` is a term iff no `s < m` that is a term has
`m - s` prime; this is a recursion on `m` (`inS`), and the terms in increasing order are the
greedy sequence above. Checked with python3: this reproduces the data, and the even terms below
`2·10^4` are exactly 0, 10, 34, 100, 310.
-/

namespace OMA.S_oeis_a025043

/-- `m` is a term of A025043: no smaller term `s` has `m - s` prime. -/
def inS (m : ℕ) : Bool :=
  (List.finRange m).all fun s => !(inS s.val) || !(decide (Nat.Prime (m - s.val)))
decreasing_by exact s.isLt

/-- The conjecture: A025043 has only finitely many even terms. -/
theorem main : {m : ℕ | inS m = true ∧ Even m}.Finite := by
  sorry

end OMA.S_oeis_a025043
