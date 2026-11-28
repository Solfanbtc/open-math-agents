import Mathlib

/-!
# A094044: Alternate prime and nonprime numbers not included earlier such that every concatenation of a pair of terms is a prime: a(2n) is nonprime and a(2n-1) is prime.

Source: https://oeis.org/A094044
Credit: @Solfanbtc

Conjecture (Robert Israel, Oct 24 2017): all members of A045572 (the numbers that are odd and
not divisible by 5, i.e. coprime to 10) are in the sequence.

Definition (greedy, as the data show). a(1) = 2; for n ≥ 2, a(n) is the least positive integer
not among a(1), ..., a(n-1) that is prime if n is odd and nonprime if n is even, and such that
the decimal concatenation a(n-1) a(n) is prime. "Every concatenation of a pair of terms" refers
to consecutive terms only, as the example explains (a(3) = 7: 97 is prime, 297 need not be).
Terms are positive (the data contain 1 as a nonprime term but never 0). Concatenation is
`a * 10^(number of digits of b) + b`. If no candidate existed the term would be `sInf ∅ = 0`.
With this definition the first 64 terms are the data 2, 9, 7, 1, 3, 49, 19, 33, ... (python3,
and `#eval` of the same rule with a bounded search); in the first 3000 terms every number
< 2000 coprime to 10 occurs (python3).
-/

namespace OMA.S_oeis_a094044

/-- Decimal concatenation of `a` and `b > 0`. -/
def concat (a b : ℕ) : ℕ := a * 10 ^ (Nat.digits 10 b).length + b

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | (n + 2) =>
    let L := terms (n + 1)
    L ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ L ∧ (m.Prime ↔ (n + 2) % 2 = 1) ∧
      (concat (L.getLastD 0) m).Prime}]

/-- A094044(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main : ∀ m : ℕ, Nat.Coprime m 10 → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a094044
