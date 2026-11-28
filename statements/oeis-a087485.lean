import Mathlib

/-!
# A087485: Odd numbers m such that 2*m - sigma(m) = 6.

Source: https://oeis.org/A087485
Credit: @Solfanbtc

The terms are the odd `m` with `2m - σ(m) = 6`, i.e. `σ(m) + 6 = 2m`, where `σ` is the sum of
divisors. Known terms: `7, 15, 315, 1155, 815634435` (e.g. `σ(15) = 24 = 2·15 - 6`), and
`a(6) > 10^24`. All known terms except the first are divisible by 15.

Conjecture (Alexander Violette, 2026): a term `a(n)` with `n > 1` and `gcd(a(n), 5) = 1` exists.
Since `a(1) = 7` is the only term below 15, "`n > 1`" means "`m ≠ 7`", i.e. `m > 7`.
(The entry's further remarks, on terms of the form `a(k) p q r …`, are proved claims, not
conjectures.)
-/

namespace OMA.S_oeis_a087485

/-- `m` is a term: odd with `2m - σ(m) = 6`. -/
def IsTerm (m : ℕ) : Prop := Odd m ∧ (∑ d ∈ m.divisors, d) + 6 = 2 * m

/-- The conjecture: some term other than `7` is coprime to `5`. -/
theorem main : ∃ m : ℕ, IsTerm m ∧ 7 < m ∧ Nat.Coprime m 5 := by
  sorry

end OMA.S_oeis_a087485
