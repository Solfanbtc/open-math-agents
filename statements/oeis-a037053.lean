import Mathlib

/-!
# A037053: Smallest prime containing exactly n 0's

Source: https://oeis.org/A037053
Credit: @Solfanbtc

`a(n)` (offset 0) is the smallest prime whose decimal representation contains exactly `n` digits
`0`: `2, 101, 1009, 10007, 100003, …` (a brute-force search with this definition reproduces the
first 6 terms; all 20 data terms have the stated digit counts). Below `a n` is the `sInf` of the
set of such primes (`0` if there were none; the conjectures concern the actual terms).

Two precise conjectures from the entry are stated, as the two parts of `main`:
1. (Robert G. Wilson v) "a prime of this form, A037053, requires at most three judiciously
   placed nonzero digits, two on the exterior and one inside": `a(n)` has at most three nonzero
   decimal digits. (The two exterior digits, first and last, are always nonzero; the content
   of the claim is the bound on the number of nonzero digits.)
2. (Bob Selcoe, Feb 20 2016, Conjecture 1) terms with two substrings of zeros have first digit
   `1`: if the decimal representation of `a(n)` has exactly two maximal runs of `0`s, its leading
   digit is `1` (e.g. `a(32) = 10^34 + 603`).
Selcoe's Conjecture 2 ("as n increases, there are more terms with two substrings of zeros than
one consecutive string") has no precise quantitative form in the entry and is not stated.
-/

namespace OMA.S_oeis_a037053

/-- Number of digits `0` in the decimal representation of `m`. -/
def zeros (m : ℕ) : ℕ := (Nat.digits 10 m).count 0

/-- A037053: the smallest prime with exactly `n` zeros in decimal. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ zeros p = n}

/-- Number of maximal runs of `0` in a digit list (the same read in either direction). -/
def zeroRuns (l : List ℕ) : ℕ :=
  ((List.range l.length).filter fun i => l.getD i 1 = 0 ∧ (i = 0 ∨ l.getD (i - 1) 1 ≠ 0)).length

/-- Leading decimal digit of `m`. -/
def leading (m : ℕ) : ℕ := (Nat.digits 10 m).getLastD 0

/-- Wilson's conjecture (at most three nonzero digits) and Selcoe's Conjecture 1. -/
theorem main :
    (∀ n : ℕ, ((Nat.digits 10 (a n)).filter (· ≠ 0)).length ≤ 3) ∧
    (∀ n : ℕ, zeroRuns (Nat.digits 10 (a n)) = 2 → leading (a n) = 1) := by
  sorry

end OMA.S_oeis_a037053
