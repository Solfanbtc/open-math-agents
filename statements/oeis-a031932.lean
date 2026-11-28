import Mathlib

/-!
# A031932: primes followed by a gap of 14; Kholdi-Firoozbakht conjecture

Source: https://oeis.org/A031932
Credit: @Solfanbtc

A031932 lists the lower primes of pairs of consecutive primes differing by `14`:
113, 293, 317, 773, 839, 863, 953, 1409, …

Conjecture (J. Kholdi and F. Firoozbakht, Nov 29 2014): "The sequence is infinite and for every n,
a(n+1) < a(n)^(1+1/n); i.e., a(n)^(1/n) is a strictly decreasing function of n."

Conventions. "Consecutive primes differing by 14" means `p` and `p + 14` are prime and no prime
lies strictly between them. Offset 1: `a(n) = Nat.nth P (n - 1)`, `n ≥ 1`. Checked with python3
for all 66762 terms below `2·10^7` (the inequality holds; the data match).
-/

namespace OMA.S_oeis_a031932

/-- `p` is prime and the next prime is `p + 14`. -/
def P (p : ℕ) : Prop := p.Prime ∧ (p + 14).Prime ∧ ∀ q, p < q → q < p + 14 → ¬ q.Prime

/-- `a(n)`, offset `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- Infinitely many terms, and `a(n+1) < a(n)^(1 + 1/n)` for every `n ≥ 1`. -/
theorem main : {p | P p}.Infinite ∧
    ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ℝ) < (a n : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a031932
