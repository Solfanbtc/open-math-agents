import Mathlib

/-!
# A076768: Positive integers not expressible as the sum of a prime and a triangular number

Source: https://oeis.org/A076768
Credit: @Solfanbtc

A076768: `1, 36, 105, 171, 210, 216, 325, …` (triangular numbers include `t(0) = 0`).

Precise conjectural claims recorded in the entry, stated as the two parts of `main`:
1. (Jonathan Vos Post and Ray Chandler, Nov 28 2004, OEIS comment) "It appears that 1, 2, 3, 8 are
   the only positive integers that cannot be partitioned as the sum of a semiprime and a triangular
   number. Here triangular numbers include `t(0) = 0` and `t(1) = 1`."
2. (T. D. Noe, Mar 26 2008, OEIS comment) the sequence "is related to the Sun's conjecture (see
   A132399) that every number except 216 is the sum of a triangular number and a prime or 0",
   i.e. the only nontriangular term of A076768 is `216`. Stated as Sun's conjecture: every natural
   number `m ≠ 216` is `t(k) + q` with `q` prime or `q = 0`.
(Noe's further remarks, that 216 is a term and that infinitely many triangular numbers are terms,
are elementary facts, and the 2004 edit's "conjecture that there are no further terms" after 9870
is refuted by the latter; neither is stated.) Python: 1 holds for `m ≤ 3·10^5`, and 2 holds for
`m ≤ 3·10^5` (with `216` the only exception).
-/

namespace OMA.S_oeis_a076768

/-- The `k`-th triangular number `k(k+1)/2`. -/
def tri (k : ℕ) : ℕ := k * (k + 1) / 2

/-- `s` is a semiprime: a product of two (not necessarily distinct) primes. -/
def IsSemiprime (s : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ s = p * q

/-- Vos Post–Chandler conjecture and Sun's conjecture. -/
theorem main :
    (∀ m : ℕ, 1 ≤ m →
      ((∃ s k : ℕ, IsSemiprime s ∧ m = s + tri k) ↔ m ∉ ({1, 2, 3, 8} : Finset ℕ))) ∧
    (∀ m : ℕ, m ≠ 216 → ∃ k q : ℕ, (q = 0 ∨ q.Prime) ∧ m = tri k + q) := by
  sorry

end OMA.S_oeis_a076768
