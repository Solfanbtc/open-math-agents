import Mathlib

/-!
# A076768: Positive integers not expressible as the sum of a prime and a triangular number

Source: https://oeis.org/A076768
Credit: @Solfanbtc

A076768: `1, 36, 105, 171, 210, 216, 325, …` (triangular numbers include `t(0) = 0`).

Conjecture (Jonathan Vos Post and Ray Chandler, Nov 28 2004, OEIS comment): "It appears that
1, 2, 3, 8 are the only positive integers that cannot be partitioned as the sum of a semiprime
and a triangular number. Here triangular numbers include `t(0) = 0` and `t(1) = 1`."

Not restated here:
* Noe's comment (Mar 26 2008) relating the sequence to Sun's conjecture (A132399: every number
  except 216 is a triangular number plus a prime or 0); that conjecture is already
  `statements/oeis-a137996.lean`.
* Noe's further remarks (216 is a term; infinitely many triangular numbers are terms), which are
  elementary facts, and the 2004 edit's "conjecture that there are no further terms" after 9870,
  which the latter refutes.

Python: the claim holds for `m ≤ 3·10^5`.
-/

namespace OMA.S_oeis_a076768

/-- The `k`-th triangular number `k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `s` is a semiprime: a product of two (not necessarily distinct) primes. -/
def IsSemiprime (s : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ s = p * q

/-- Vos Post–Chandler conjecture. -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    ((∃ s k : ℕ, IsSemiprime s ∧ m = s + tri k) ↔ m ∉ ({1, 2, 3, 8} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a076768
