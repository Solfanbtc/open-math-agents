import Mathlib

/-!
# A050972: Smaller member of friendly pairs ordered by smallest maximal element.

Source: https://oeis.org/A050972
Credit: @Solfanbtc

Conjecture (Jaycob Coleman, OEIS A050972, comment, Sep 27 2014): if a(n) is in A005153
(practical numbers), then A050973(n) is in A005153. (The accompanying question about a
generalized indicator function m(n) does not specify m and is not stated.)

Conventions:
* A friendly pair is m < n, both positive, with the same abundancy σ(m)/m = σ(n)/n, written
  σ(m)·n = σ(n)·m. a(n) and A050973(n) are the smaller and larger members of the n-th pair (the
  pairs are listed with all their members, e.g. both (6, 28) and (6, 496)), so the conjecture
  is about every friendly pair.
* Practical number (A005153, %N): a positive integer m such that every k ≤ σ(m) is a sum of
  distinct divisors of m.
* Checked in Python: the pairs ordered by larger member reproduce %S; for all 5769 friendly
  pairs with larger member ≤ 3·10^5, the larger member is practical whenever the smaller one
  is (practicality tested with Stewart's criterion).
-/

namespace OMA.S_oeis_a050972

/-- `σ(m)`, the sum of the divisors of `m`. -/
def sigma (m : ℕ) : ℕ := ∑ d ∈ m.divisors, d

/-- Practical number: every `k ≤ σ(m)` is a sum of distinct divisors of `m`. -/
def IsPractical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k ≤ sigma m, ∃ S ⊆ m.divisors, ∑ d ∈ S, d = k

/-- `m < n` is a friendly pair. -/
def Friendly (m n : ℕ) : Prop := 0 < m ∧ m < n ∧ sigma m * n = sigma n * m

/-- Coleman's conjecture: in a friendly pair, if the smaller member is practical, so is the
larger. -/
theorem main : ∀ m n : ℕ, Friendly m n → IsPractical m → IsPractical n := by
  sorry

end OMA.S_oeis_a050972
