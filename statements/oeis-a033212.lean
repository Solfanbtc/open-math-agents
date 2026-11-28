import Mathlib

/-!
# A033212: Primes congruent to 1 or 19 (mod 30).

Source: https://oeis.org/A033212
Credit: @Solfanbtc

Status: solved. The entry records three statements, first posed as conjectures and now theorems
by the work of J. B. Tunnell ("Proofs of Conjectures Concerning Entry A033212", linked from the
entry, https://oeis.org/A033212/a033212.txt):

1. (T. D. Noe, Apr 29 2008) The primes p ≡ 1 or 19 (mod 30) are the same as the primes of the
   form x^2 - xy + 4y^2 (discriminant -15) and the same as the primes of the form
   x^2 - xy + 19y^2 (discriminant -75), both with x and y nonnegative.
2. (T. D. Noe, Apr 29 2008) The same as primes of the form x^2 + xy + 19y^2 (discriminant -75),
   with x and y nonnegative.
3. (N. J. A. Sloane, Jun 01 2014) The same as primes of the form x^2 + 5xy - 5y^2
   (discriminant 45).

Translation notes.
* Statement 1 is read as two separate equalities of sets of primes (each form on its own);
  checked numerically for p < 20000. Their intersection reading follows from it.
* Statement 2, read literally with x, y ≥ 0, is false: 919 = 30 * 30 + 19 is prime, but
  x^2 + xy + 19y^2 = 919 has no solution in nonnegative integers (y ≤ 6, checked by hand and
  by computer). Minimal fix: x and y range over all integers, which is the usual meaning of
  "primes of the form" for a binary quadratic form; this version holds numerically for p < 20000.
* Statement 3 has no sign condition, so x and y are integers.
-/

namespace OMA.S_oeis_a033212

/-- Membership in A033212: a prime congruent to 1 or 19 modulo 30. -/
def InA033212 (p : ℕ) : Prop := p.Prime ∧ (p % 30 = 1 ∨ p % 30 = 19)

theorem main :
    (∀ p : ℕ, p.Prime →
      (InA033212 p ↔ ∃ x y : ℕ, (p : ℤ) = (x : ℤ) ^ 2 - x * y + 4 * (y : ℤ) ^ 2)) ∧
    (∀ p : ℕ, p.Prime →
      (InA033212 p ↔ ∃ x y : ℕ, (p : ℤ) = (x : ℤ) ^ 2 - x * y + 19 * (y : ℤ) ^ 2)) ∧
    (∀ p : ℕ, p.Prime →
      (InA033212 p ↔ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + x * y + 19 * y ^ 2)) ∧
    (∀ p : ℕ, p.Prime →
      (InA033212 p ↔ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + 5 * x * y - 5 * y ^ 2)) := by
  sorry

end OMA.S_oeis_a033212
