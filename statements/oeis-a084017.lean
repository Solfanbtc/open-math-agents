import Mathlib

/-!
# A084017: Smallest n-digit palindromic multiple of n with digit sum a multiple of n

Source: https://oeis.org/A084017
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest `n`-digit palindromic multiple of `n` whose digit sum is also a
multiple of `n`; "for `n = 10k` it is sufficient that the multiple is palindromic with leading zeros
ignored" (such a number ends in `0`, and it is palindromic once leading zeros are allowed, i.e.
its digit string with the trailing zeros removed is a palindrome, e.g. `a(10) = 1000800010`,
`100080001` being a palindrome); `0` if no such number exists:
`1, 22, 111, 4004, 50005, 201102, …` (a search with this reading reproduces the first 12 data
terms, including `a(10)`).

Conjecture (OEIS comment): no entry is zero, i.e. for every `n ≥ 1` such a number exists.
-/

namespace OMA.S_oeis_a084017

/-- A list is a palindrome. -/
def Pal (l : List ℕ) : Prop := l.reverse = l

/-- `m` is an admissible `n`-digit number for A084017 (`Nat.digits` lists the least significant
digit first, so trailing zeros of `m` are the leading entries of the list). -/
def Good (n m : ℕ) : Prop :=
  10 ^ (n - 1) ≤ m ∧ m < 10 ^ n ∧ n ∣ m ∧ n ∣ (Nat.digits 10 m).sum ∧
    (if n % 10 = 0 then Pal ((Nat.digits 10 m).dropWhile (· = 0)) else Pal (Nat.digits 10 m))

/-- No entry of A084017 is zero. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, Good n m := by
  sorry

end OMA.S_oeis_a084017
