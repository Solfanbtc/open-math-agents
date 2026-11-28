import Mathlib

/-!
# A100570: numbers that are not the sum of a square and a semiprime

Source: https://oeis.org/A100570
A100570 lists the positive integers that are not of the form `k^2 + s` with `k ≥ 0` and `s` a
semiprime (a product of two primes, not necessarily distinct: `Ω(s) = 2`, A001358):
1, 2, 3, 12, 17, 28, 32, 72, 108, 117, 297, 657.
The entry: "It appears that this sequence is finite ... There are probably no further exceptions
after a(12)=657", and (V. Shevelev) "The statement about the finiteness of this sequence (namely,
a(n)<=657) is much stronger than the Goldbach binary conjecture." There are no new terms up to
2^28 (D. Mikhail).

We state the conjecture that the sequence is exactly the twelve listed terms: a positive
integer `m` is not a square plus a semiprime iff `m` is one of them. (This includes the weaker
conjecture in the entry, that the sequence contains no perfect square `> 1`.)
Squares include `0^2 = 0`, as in the entry's Mathematica program (`i` from 0) and its example for
`m = 12`. Checked with python3: up to `10^6` the exceptions are exactly the twelve listed numbers.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a100570

/-- `m` is the sum of a square and a semiprime. -/
def IsSqPlusSemiprime (m : ℕ) : Prop :=
  ∃ k s : ℕ, ArithmeticFunction.cardFactors s = 2 ∧ m = k ^ 2 + s

theorem main : ∀ m : ℕ, 1 ≤ m →
    (¬ IsSqPlusSemiprime m ↔ m ∈ ({1, 2, 3, 12, 17, 28, 32, 72, 108, 117, 297, 657} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a100570
