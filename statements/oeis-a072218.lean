import Mathlib

/-!
# A072218: Consider the Reverse and Add! problem (cf. A001127); of all the n-digit numbers N which eventually reach a palindrome, pick that number N which takes the greatest number of steps to converge (in case of a tie, pick the smallest N); sequence gives palindrome that is reached.

Source: https://oeis.org/A072218
Credit: @Solfanbtc

Reverse and Add: `R x = x + reverse(x)` in base 10. A number `N` converges in `k` steps when
`k ≥ 1` and `R^[k] N` is the first palindrome among `R^[1] N, R^[2] N, …`. At least one step is
counted: the term for `n = 1` is 11 (from `N = 5`: 5 → 10 → 11, 2 steps), although one-digit
numbers are themselves palindromes. For each `n`, among the `n`-digit `N`
(`10^(n-1) ≤ N < 10^n`) that converge, take the `N` with the most steps (on a tie, the smallest
`N`); `a(n)` is the palindrome it reaches.

Comment in the entry: "Since we do not even know if 196 eventually converges (see A006960,
A023108) for n >= 3 these values are only conjectures": a number not known to converge could
converge after more steps and change the record. `main` states that the listed data terms
`a(1), …, a(9)` are correct: for each `n ≤ 9` there is an `n`-digit `N` converging in `k` steps
to the listed palindrome, such that every `n`-digit `N'` converging in `k'` steps has `k' < k`, or
`k' = k` and `N ≤ N'`. The terms for `n = 1, 2` are known (every number below 196 converges).

Checked with python3 (numbers not converging within 300 steps treated as non-convergent) for
`n ≤ 5`: records 5 (2 steps), 89 (24), 187 (23), 1297 (21), 10911 (55), reaching exactly the listed
values.
-/

namespace OMA.S_oeis_a072218

/-- Reverse the base-10 digits. -/
def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Reverse and Add. -/
def R (x : ℕ) : ℕ := x + rev x

/-- `x` is a base-10 palindrome. -/
def IsPal (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- `N` reaches its first palindrome after exactly `k ≥ 1` steps of Reverse and Add. -/
def ConvergesIn (N k : ℕ) : Prop :=
  1 ≤ k ∧ IsPal (R^[k] N) ∧ ∀ j, 1 ≤ j → j < k → ¬ IsPal (R^[j] N)

/-- The data of A072218, `a(1), …, a(9)`. -/
def data : List ℕ :=
  [11, 8813200023188, 8813200023188, 8813200023188, 4668731596684224866951378664,
    682049569465550121055564965940286,
    555458774083726674580862268085476627380477854555,
    555458774083726674580862268085476627380477854555,
    1345428953367763125675365555635765213677633598245431]

/-- `v` is the palindrome reached by the record holder among the `n`-digit numbers. -/
def IsTerm (n v : ℕ) : Prop :=
  ∃ N k, 10 ^ (n - 1) ≤ N ∧ N < 10 ^ n ∧ ConvergesIn N k ∧ R^[k] N = v ∧
    ∀ N' k', 10 ^ (n - 1) ≤ N' → N' < 10 ^ n → ConvergesIn N' k' →
      k' < k ∨ (k' = k ∧ N ≤ N')

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 9 → IsTerm n (data.getD (n - 1) 0) := by
  sorry

end OMA.S_oeis_a072218
