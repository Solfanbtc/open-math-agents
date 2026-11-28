import Mathlib

/-!
# A082613: Smallest palindrome divisible by an n-th power

Source: https://oeis.org/A082613
Credit: @Solfanbtc

`a(n)` (offset 0) is the smallest (positive, decimal) palindrome divisible by an `n`-th power
`m^n` with `m ≥ 2` (for `n = 0` every number qualifies, `a(0) = 1`): `1, 2, 4, 8, 272, 2112, 2112,
4224, …` (a search with this definition reproduces the first 15 data terms).

Conjecture (OEIS comment): "the `n`-th power that divides `a(n)` is `2^n`", i.e. `2^n ∣ a(n)`.
(Equivalently, `a(n)` is the smallest palindrome divisible by `2^n`.) Stated for all `n`; all 28
data terms satisfy it.
-/

namespace OMA.S_oeis_a082613

/-- `x` is a decimal palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- A082613: the smallest positive palindrome divisible by `m^n` for some `m ≥ 2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | 0 < x ∧ IsPal x ∧ ∃ m : ℕ, 2 ≤ m ∧ m ^ n ∣ x}

/-- The `n`-th power dividing `a(n)` is `2^n`. -/
theorem main : ∀ n : ℕ, 2 ^ n ∣ a n := by
  sorry

end OMA.S_oeis_a082613
