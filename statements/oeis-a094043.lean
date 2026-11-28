import Mathlib

/-!
# A094043: Alternate composite and prime numbers not included earlier such that every partial concatenation is a prime: a(2n) is prime and a(2n-1) is not prime.

Source: https://oeis.org/A094043
Credit: @Solfanbtc

The sequence is greedy, starting from `a(1) = 1` (whose concatenation "1" is accepted: the
example lists 1, 13, 139, 13913, ... as "not composite"). For `n ≥ 2`, `a(n)` is the least
positive integer not used before, prime if `n` is even and not prime if `n` is odd, such that the
decimal concatenation `a(1) a(2) ⋯ a(n)` is prime. `firstTerms n = [a(1), …, a(n)]`. Checked with
python3: this reproduces the 57 listed terms 1, 3, 9, 13, 63, 107, 27, ...

Conjecture (R. G. Wilson v): 2 and 5 are the only two (positive) nonmembers. (They can never
occur, since a longer concatenation ending in 2 or 5 is composite.) `main` states that every
positive integer other than 2 and 5 occurs.
-/

namespace OMA.S_oeis_a094043

/-- Decimal concatenation of the entries of `l`. -/
def concat (l : List ℕ) : ℕ := l.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

/-- `firstTerms n = [a(1), …, a(n)]` for `n ≥ 1`. -/
noncomputable def firstTerms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := firstTerms (n + 1)
    l ++ [sInf {x : ℕ | 1 ≤ x ∧ x ∉ l ∧ (x.Prime ↔ Even (n + 2)) ∧ (concat (l ++ [x])).Prime}]

/-- `a n`: the `n`-th term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (firstTerms n).getD (n - 1) 0

theorem main : ∀ m : ℕ, 1 ≤ m → m ≠ 2 → m ≠ 5 → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a094043
