import Mathlib

/-!
# A006960: Reverse and Add! sequence starting with 196.

Source: https://oeis.org/A006960
Credit: @Solfanbtc

`a(0) = 196`, `a(n+1) = a(n) + reverse(a(n))` (base 10).

Conjecture (A006960): 196 is the smallest initial term which does not lead to a palindrome.

Formalized as two parts: no term of A006960 is a base-10 palindrome, and every positive
`x < 196` leads to a palindrome, i.e. some iterate `T^[k] x` (`k ≥ 0`) of reverse-and-add is a
palindrome. The `k ≥ 0` convention is the one of A023108, where the same conjecture is listed;
a computer check shows every `0 < x < 196` reaches a palindrome within 24 steps, also when
`k ≥ 1` is required, so the choice does not change the content. The same claim is stated as
`OMA.S_oeis_a023108.main`; here it is phrased through the A006960 sequence itself.
-/

namespace OMA.S_oeis_a006960

/-- Reverse the base-10 digits. -/
def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Reverse-and-add. -/
def T (x : ℕ) : ℕ := x + rev x

/-- `x` is a base-10 palindrome. -/
def IsPalindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- A006960: `a 0 = 196`, `a (n+1) = a n + reverse (a n)`. -/
def a (n : ℕ) : ℕ := T^[n] 196

theorem main :
    (∀ n : ℕ, ¬ IsPalindrome (a n)) ∧
      ∀ x : ℕ, 0 < x → x < 196 → ∃ k, IsPalindrome (T^[k] x) := by
  sorry

end OMA.S_oeis_a006960
