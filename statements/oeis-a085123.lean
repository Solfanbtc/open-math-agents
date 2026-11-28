import Mathlib

/-!
# A085123: Smallest member of A002473 whose digital product = A002473(n), or 0 if no such number exists.

Source: https://oeis.org/A085123
Credit: @Solfanbtc

A002473 is the 7-smooth numbers `1, 2, 3, …, 9, 10, 12, …` (positive integers with no prime
factor above `7`). The digital product of `k` is the product of its decimal digits. `a(n)` is
the least 7-smooth `k` with digital product `A002473(n)`, or `0` if there is none. (Python
reproduces the data `1, 2, …, 9, 25, 126, 27, 35, 28, 36, 45, 0, 64`, searching `k < 10^6`.)

Conjecture (Amarnath Murthy, in the entry): no entry is zero, i.e. every 7-smooth `m` is the
digital product of some 7-smooth number.

Status: false. Robert Israel (comment of Nov 23 2019) showed `a(17) = 0`: `A002473(17) = 21`,
and the last two digits of every 7-smooth number greater than `7` include a digit other than
`1, 3, 7`, while a number with digital product `21` has only such digits (so it would be at
most `7` or have two such final digits). More generally `a(n) = 0` whenever `n ≥ 17` and
`A002473(n)` is coprime to `10`. The statement below is the conjecture as posed, so its
negation is what can be proved.
-/

namespace OMA.S_oeis_a085123

/-- `n` is 7-smooth (a term of A002473). -/
def Smooth7 (n : ℕ) : Prop := 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 7

/-- The conjecture: every 7-smooth number is the digital product of a 7-smooth number. -/
theorem main : ∀ m : ℕ, Smooth7 m → ∃ k : ℕ, Smooth7 k ∧ (Nat.digits 10 k).prod = m := by
  sorry

end OMA.S_oeis_a085123
