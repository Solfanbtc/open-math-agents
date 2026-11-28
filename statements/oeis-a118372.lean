import Mathlib

/-!
# A118372: S-perfect numbers.

Source: https://oeis.org/A118372
Credit: @Solfanbtc

Granville's set `S` (De Koninck: "Granville numbers"): `1 ∈ S`, and for `n > 1`, `n ∈ S` iff
`Σ_{d ∣ n, d < n, d ∈ S} d ≤ n`. A positive `n ∈ S` is S-perfect when that sum equals `n`
(6, 24, 28, 96, 126, 224, …). The definition below is the same recursion for every `n`
(for `n = 1` the sum is empty, so `1 ∈ S`); `0` is excluded from the S-perfect numbers.

A Zumkeller number (A083207) is an `m` whose divisors can be partitioned into two disjoint sets
with equal sum, i.e. some set `A` of divisors of `m` has `Σ A = Σ (divisors m \ A)`.

Conjecture (Ivan N. Ianakiev, 2017): if `k` is S-perfect then `σ(k)/2` is a Zumkeller number.
`main` also asserts that `σ(k)` is even, which the conjecture presupposes. Checked with python3:
the definition gives the listed terms below 30000, and the conjecture holds for the listed
terms up to 5540590.
-/

namespace OMA.S_oeis_a118372

/-- Membership in Granville's set `S`. -/
def InS (n : ℕ) : Bool :=
  decide ((∑ d ∈ n.properDivisors.attach.filter (fun d => InS d.1), d.1) ≤ n)
termination_by n
decreasing_by all_goals exact (Nat.mem_properDivisors.mp (Subtype.property _)).2

/-- `n` is S-perfect (A118372). -/
def IsSPerfect (n : ℕ) : Prop :=
  0 < n ∧ (∑ d ∈ n.properDivisors.attach.filter (fun d => InS d.1), d.1) = n

/-- `m` is a Zumkeller number (A083207). -/
def IsZumkeller (m : ℕ) : Prop :=
  ∃ A ⊆ m.divisors, ∑ d ∈ A, d = ∑ d ∈ m.divisors \ A, d

/-- Ianakiev's conjecture. -/
theorem main : ∀ k : ℕ, IsSPerfect k →
    2 ∣ (ArithmeticFunction.sigma 1 k) ∧ IsZumkeller (ArithmeticFunction.sigma 1 k / 2) := by
  sorry

end OMA.S_oeis_a118372
