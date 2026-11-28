import Mathlib

/-!
# A089337: a(1) = 1; for n > 1, a(n) is the smallest number that is either a divisor or a multiple, in that priority (order), of a(n-1) such that it is a distinct palindrome not included earlier.

Source: https://oeis.org/A089337
Credit: @Solfanbtc

Conjecture (OEIS A089337): every palindrome is a member.

Definition (offset 1): a(1) = 1; for n > 1, if some palindrome dividing a(n-1) has not appeared
among a(1), ..., a(n-1), then a(n) is the least such; otherwise a(n) is the least positive
palindromic multiple of a(n-1) not appeared earlier ("divisor or multiple, in that priority").
Palindromes are in base 10 (digit list equal to its reverse). `main` quantifies over every
sequence satisfying this specification (exactly one does; `a 0` is unused) and states that every
positive palindrome m equals some a(n), n >= 1.
Checked numerically: the rule reproduces the listed terms 1, 2, 4, 8, 88, 11, 22, 44, 484, 121, ...
-/

namespace OMA.S_oeis_a089337

/-- `x` is a decimal palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- The defining rule of A089337. -/
def Spec (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
    let fresh := fun p : ℕ => IsPal p ∧ 0 < p ∧ ∀ j, 1 ≤ j → j < n → a j ≠ p
    ((∃ p, fresh p ∧ p ∣ a (n - 1)) →
        IsLeast {p | fresh p ∧ p ∣ a (n - 1)} (a n)) ∧
    ((¬ ∃ p, fresh p ∧ p ∣ a (n - 1)) →
        IsLeast {p | fresh p ∧ a (n - 1) ∣ p} (a n))

theorem main : ∀ a : ℕ → ℕ, Spec a → ∀ m : ℕ, 0 < m → IsPal m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a089337
