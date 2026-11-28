import Mathlib

/-!
# A083834: Palindromes of the form 5p + 1 where p is also a palindrome. Palindromes arising in A083833.

Source: https://oeis.org/A083834
Credit: @Solfanbtc

The terms are the decimal palindromes `t = 5p + 1` with `p` a positive decimal palindrome.

Conjectures (Michael S. Branicky, 2021):
1. all terms contain only the digits 0, 1, 5, 6;
2. "for d odd, the only term with d digits is 1^d; equivalently, all terms starting with 6 have
   odd length".
The first sentence of 2 is contradicted by the first terms 6 and 606 (odd length, not
repunits), while its "equivalent" form agrees with the data; the intended statement is
clearly "for d even": all even-length terms (1111, 111111, 11111111, ...) are repunits.
Minimal fix used here: `d` even. We state both forms of 2 (they are equivalent given
Branicky's observation that every term starts with 1 or 6).
We checked by computer, for all palindromes `p < 10^7`, that the terms found agree with
%S, %T, %U and satisfy 1 and both forms of 2.
-/

namespace OMA.S_oeis_a083834

/-- `n` is a decimal palindrome. -/
def IsPal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- The terms of A083834. -/
def IsTerm (t : ℕ) : Prop := IsPal t ∧ ∃ p : ℕ, 0 < p ∧ IsPal p ∧ t = 5 * p + 1

/-- Branicky's conjectures (with `d` even, see above). -/
theorem main :
    (∀ t, IsTerm t → ∀ d ∈ Nat.digits 10 t, d = 0 ∨ d = 1 ∨ d = 5 ∨ d = 6) ∧
    (∀ t, IsTerm t → Even (Nat.digits 10 t).length → ∀ d ∈ Nat.digits 10 t, d = 1) ∧
    (∀ t, IsTerm t → (Nat.digits 10 t).getLast? = some 6 → Odd (Nat.digits 10 t).length) := by
  sorry

end OMA.S_oeis_a083834
