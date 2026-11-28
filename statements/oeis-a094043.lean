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

Conjecture (R. G. Wilson v): 2 and 5 are the only two (positive) nonmembers. Read literally this
is trivially false: for `n ≥ 2` the concatenation `a(1) ⋯ a(n)` has at least two digits and ends
with the digits of `a(n)`, so it can only be prime if `a(n)` is odd and does not end in 5. Hence
no even number and no multiple of 5 ever occurs (and `a(1) = 1`): 2, 4, 5, 6, 8, 10, 15, ... are
all nonmembers, not just 2 and 5. The minimal fix states the evidently intended claim: the members
are exactly the positive integers coprime to 10. `main` states that every `m ≥ 1` with
`gcd(m, 10) = 1` occurs, together with the (easy) converse.
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

theorem main : ∀ m : ℕ, 1 ≤ m → ((∃ n : ℕ, 1 ≤ n ∧ a n = m) ↔ Nat.Coprime m 10) := by
  sorry

end OMA.S_oeis_a094043
