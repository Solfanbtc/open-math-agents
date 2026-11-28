import Mathlib

/-!
# A084015: Largest n-digit palindromic multiple of n. For n = 10k it is sufficient that the multiple is palindromic with leading zeros ignored. 0 if no such number exists.

Source: https://oeis.org/A084015
Credit: @Solfanbtc

An admissible number for `n` is an `n`-digit number `x` (`10^(n-1) ≤ x < 10^n`) that is a multiple
of `n` and is a palindrome in base 10. When `10 ∣ n`, the name relaxes this to "palindromic
with leading zeros ignored": `x = P · 10^s` with `P` a palindrome, i.e. `x` reads as a palindrome
when written with `s` leading zeros (e.g. `a(10) = 9999999990`). `a(n)` is the largest
admissible number, or 0 if there is none. Checked with python3: this gives the data for
`n ≤ 8` and `n = 10`.

Conjecture (in the entry): no entry is zero, i.e. for every `n ≥ 1` an admissible number exists.
`main` states this.
-/

namespace OMA.S_oeis_a084015

/-- `x` is a base-10 palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- `x` is an admissible `n`-digit palindromic multiple of `n`. -/
def Admissible (n x : ℕ) : Prop :=
  10 ^ (n - 1) ≤ x ∧ x < 10 ^ n ∧ n ∣ x ∧
    (if 10 ∣ n then ∃ P s : ℕ, x = P * 10 ^ s ∧ IsPal P else IsPal x)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ x : ℕ, Admissible n x := by
  sorry

end OMA.S_oeis_a084015
