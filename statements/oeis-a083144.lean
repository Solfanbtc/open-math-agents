import Mathlib

/-!
# A083144: Smallest k such that k*prime(n) is an n-digit palindrome, or 0 if no such number exists.

Source: https://oeis.org/A083144
Credit: @Solfanbtc

Conjecture (OEIS A083144): no entry is zero, i.e. for every n >= 1 (offset 1) some positive
multiple k * prime(n) is a palindrome with exactly n decimal digits.

Conventions: prime(n) = `Nat.nth Nat.Prime (n - 1)`; x has n digits iff `(Nat.digits 10 x).length = n`;
a palindrome is a number whose digit list equals its reverse. Examples from the data:
1 * 2 = 2, 11 * 3 = 33, 101 * 5 = 505, 143 * 7 = 1001, 991 * 11 = 10901.
-/

namespace OMA.S_oeis_a083144

/-- `x` is a decimal palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧
    IsPal (k * Nat.nth Nat.Prime (n - 1)) ∧
    (Nat.digits 10 (k * Nat.nth Nat.Prime (n - 1))).length = n := by
  sorry

end OMA.S_oeis_a083144
