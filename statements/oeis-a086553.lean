import Mathlib

/-!
# A086553: smallest unused number with a(n) + 1 and a(n) a(n-1) + 1 prime

Source: https://oeis.org/A086553
Credit: @Solfanbtc

`a(1) = 1`, and `a(n)` is the smallest (positive) number not included earlier such that both
`a(n) + 1` and `a(n) a(n-1) + 1` are primes: `1, 2, 6, 10, 4, 18, 22, …` (this greedy rule reproduces
all 59 data terms). Below `terms k = [a(1), …, a(k+1)]`.

Conjecture (OEIS comment): every number `p - 1`, `p` prime, is a term.
-/

namespace OMA.S_oeis_a086553

/-- The greedy next term after the terms `l`. -/
noncomputable def next (l : List ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ m ∉ l ∧ (m + 1).Prime ∧ (m * l.getLastD 0 + 1).Prime}

/-- `terms k = [a(1), …, a(k+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => terms k ++ [next (terms k)]

/-- For every prime `p`, `p - 1` occurs in A086553. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ k : ℕ, p - 1 ∈ terms k := by
  sorry

end OMA.S_oeis_a086553
