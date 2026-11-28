import Mathlib

/-!
# A083476: Positions of 0's in A083475.

Source: https://oeis.org/A083476
Credit: @Solfanbtc

Strong conjecture (OEIS A083476): there are only finitely many terms in this sequence not divisible
by 10.

Definitions: A083475(n) is the number of palindromes (in base 10) among n*k, 1 <= k <= n; this
sequence lists the n >= 1 where that number is 0. A palindrome is a number whose decimal digit list
equals its reverse. `main`: the set of n >= 1, not divisible by 10, such that no n*k with
1 <= k <= n is a palindrome, is finite.
Checked numerically: the listed terms are reproduced. Note: below 3000 there are still 446 such n
not divisible by 10 (the largest being 2997), so the numerical evidence for finiteness is weak; the
statement is the one recorded in the entry.
-/

namespace OMA.S_oeis_a083476

/-- `x` is a decimal palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ 10 ∣ n ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n → ¬ IsPal (n * k)}.Finite := by
  sorry

end OMA.S_oeis_a083476
