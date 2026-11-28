import Mathlib

/-!
# A090521: Least k such that floor(n!/k) is prime.

Source: https://oeis.org/A090521
Credit: @Solfanbtc

`a(n)` (offset 2) is the least positive integer `k` such that `⌊n! / k⌋` is prime (natural-number
division is the floor). Example: `a(5) = 7`, since 120, 60, 40, 30, 24, 20 are not prime and
`⌊120/7⌋ = 17` is.

Conjecture (A. Murthy, 2003): there exists a number `K` such that `a(n)` is prime for all `n > K`.
`main` states this. The entry also records the opposite conjecture (C. R. Greathouse IV, 2013):
"there are infinitely many composites in this sequence" (heuristically of density 1). That is
exactly the negation of `main`, so it amounts to a disproof of `main`. (The data already contain
many composite terms: 22, 74, 76, 49, 95, ...)
-/

namespace OMA.S_oeis_a090521

/-- `a n`: the least `k ≥ 1` with `⌊n! / k⌋` prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ (n.factorial / k).Prime}

theorem main : ∃ K : ℕ, ∀ n : ℕ, K < n → (a n).Prime := by
  sorry

end OMA.S_oeis_a090521
