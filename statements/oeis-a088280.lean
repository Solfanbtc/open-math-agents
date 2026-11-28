import Mathlib

/-!
# A088280: Noncomposites in A088279.

Source: https://oeis.org/A088280
Credit: @Solfanbtc

Conjecture (OEIS A088280): the sequence is finite, i.e. only finitely many terms of A088279 are
noncomposite (1 or prime). Known terms: 1, 1300000000031, 17000000000000071 (the next one, if any,
has more than 1000 digits).

Definitions: A088279(n), for n >= 1, is the smallest n-digit palindrome beginning with n: its
decimal digit string has length n, starts with the digit string of n, and reads the same
backwards (1, 22, 303, 4004, ..., 1000000001, ...). Such a palindrome exists for every n >= 1
(n has at most n digits). `main`: the set of n >= 1 for which A088279(n) is 1 or prime is finite
(it then contains exactly n = 1, 13, 17 among the n giving the known terms).
-/

namespace OMA.S_oeis_a088280

/-- `x` is a decimal palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- A088279(n): the smallest `n`-digit palindrome whose decimal expansion begins with that of `n`. -/
noncomputable def A088279 (n : ℕ) : ℕ :=
  sInf {x : ℕ | IsPal x ∧ (Nat.digits 10 x).length = n ∧
    (Nat.digits 10 n).reverse <+: (Nat.digits 10 x).reverse}

theorem main : {n : ℕ | 1 ≤ n ∧ (A088279 n = 1 ∨ (A088279 n).Prime)}.Finite := by
  sorry

end OMA.S_oeis_a088280
