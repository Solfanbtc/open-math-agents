import Mathlib

/-!
# A030057: Least number that is not a sum of distinct divisors of n.

Source: https://oeis.org/A030057
Credit: @Solfanbtc

`a(n)` (offset 1) is the least positive integer that is not a sum of distinct divisors of `n`:
`2, 4, 2, 8, 2, 13, 2, 16, 2, 4, ...`.

Claim (Amiram Eldar, Jun 13 2020, as recorded in the entry): the indices of records of `a` occur
at the highly abundant numbers (A002093), excluding 3 and 10, *if* Jaycob Coleman's conjecture at
A002093 (every highly abundant number `> 10` is practical, A005153) is true. The claim is
conditional, so it is stated as the implication
`Coleman's conjecture → {record indices of a} = {highly abundant numbers} \ {3, 10}`.

A python3 check up to `n = 20000`: the record indices are `1, 2, 4, 6, 8, 12, 16, 18, 20, 24, ...`,
equal to the highly abundant numbers `1, 2, 3, 4, 6, 8, 10, 12, ...` minus `{3, 10}`; the only
highly abundant numbers in that range that are not practical are `3` and `10`.

Conventions:
* "sum of distinct divisors": `∑ d ∈ s, d` for some `s ⊆ n.divisors` (the empty sum gives `0`,
  so the least non-representable number is positive automatically; it exists, as `σ(n) + 1` is
  not representable).
* A record index is `n ≥ 1` with `a m < a n` for all `1 ≤ m < n` (so `n = 1` is a record, as in
  the data: `1` is the first highly abundant number). Highly abundant: `n ≥ 1` with
  `σ(m) < σ(n)` for all `1 ≤ m < n` (A002093).
* Practical (A005153): `n ≥ 1` and every `1 ≤ m < n` is a sum of distinct divisors of `n`.
-/

namespace OMA.S_oeis_a030057

/-- `m` is a sum of distinct divisors of `n`. -/
def IsSumDistinctDivisors (n m : ℕ) : Prop := ∃ s ⊆ n.divisors, ∑ d ∈ s, d = m

/-- `a n = A030057(n)`: the least number that is not a sum of distinct divisors of `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ¬ IsSumDistinctDivisors n m}

/-- Highly abundant numbers (A002093): `σ(n)` exceeds `σ(m)` for every `1 ≤ m < n`. -/
def IsHighlyAbundant (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → ArithmeticFunction.sigma 1 m < ArithmeticFunction.sigma 1 n

/-- Practical numbers (A005153). -/
def IsPractical (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → IsSumDistinctDivisors n m

/-- `n` is the index of a record of `a`. -/
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m, 1 ≤ m → m < n → a m < a n

/-- Coleman's conjecture (a) at A002093: every highly abundant number `> 10` is practical. -/
def ColemanConjecture : Prop := ∀ n, IsHighlyAbundant n → 10 < n → IsPractical n

/-- If Coleman's conjecture holds, the record indices of A030057 are exactly the highly abundant
numbers other than 3 and 10. -/
theorem main : ColemanConjecture →
    {n | IsRecord n} = {n | IsHighlyAbundant n} \ {3, 10} := by
  sorry

end OMA.S_oeis_a030057
