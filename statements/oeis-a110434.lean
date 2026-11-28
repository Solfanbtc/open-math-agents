import Mathlib

/-!
# A110434: every number ending in 1, 3, 7 or 9 occurs in the prime-concatenation sequence

Source: https://oeis.org/A110434
"Distinct numbers with least significant digit following the repetitive pattern
1,3,7,9,1,3,7,9,... such that every partial concatenation is a prime": 11, 3, 17, 49, 51, 93, ...
(11, 113, 11317, 1131749, ... are prime). Each term is the least number not used before, with the
prescribed last digit, whose decimal concatenation to the previous terms is prime (this greedy
rule reproduces the data).
Conjecture of the entry: "every number == 1,3,7,9 (mod 10) is a term."

Formalization. `terms n` is the list of the first `n` terms; the `(n+1)`-st term is the least `x`
not among them with `x ≡ [1,3,7,9][n mod 4] (mod 10)` such that the concatenation of the terms
and `x` is prime (`sInf`; if no such `x` existed the term would be `0`, which is never one of the
numbers of the conjecture). The conjecture: every `m` with `m mod 10 ∈ {1, 3, 7, 9}` is in
`terms n` for some `n`.
Checked with python3 (Miller-Rabin): the greedy rule reproduces all 53 listed terms.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a110434

/-- Decimal concatenation of a list of natural numbers. -/
def concat (l : List ℕ) : ℕ :=
  l.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

/-- The prescribed last digit of the `(n+1)`-st term. -/
def pat (n : ℕ) : ℕ := [1, 3, 7, 9].getD (n % 4) 0

/-- The first `n` terms of A110434. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    terms n ++ [sInf {x : ℕ | x ∉ terms n ∧ x % 10 = pat n ∧ (concat (terms n ++ [x])).Prime}]

theorem main : ∀ m : ℕ, (m % 10 = 1 ∨ m % 10 = 3 ∨ m % 10 = 7 ∨ m % 10 = 9) →
    ∃ n : ℕ, m ∈ terms n := by
  sorry

end OMA.S_oeis_a110434
