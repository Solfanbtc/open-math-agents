import Mathlib

/-!
# A038667: Minimal value of |product(A) - product(B)| where A and B are a partition of {1,2,3,...,n}.

Source: https://oeis.org/A038667
Credit: @Solfanbtc

Conjecture (Richard Peterson, OEIS A038667, comment, Jul 13 2023): the sequence of rational
numbers A061057(n)/a(n) has 1 as a limit point. (The accompanying question, which other limit
points there are, asks for a value and is not stated.)

Conventions:
* a(n) (offset 0) is the minimum of |∏A - ∏B| over all partitions {1..n} = A ⊔ B (empty
  parts allowed, empty product 1): a(0) = 0, a(1) = 0, a(2) = 1, a(13) = 576, ...
* A061057(n) (offset 1): write n! = x*y with x ≤ y and x maximal; A061057(n) = y - x. Here x is
  the largest divisor of n! with x^2 ≤ n!.
* "has 1 as a limit point" is read as: 1 is a cluster point (accumulation point) of the
  sequence n ↦ A061057(n)/a(n), i.e. for every ε > 0, |A061057(n)/a(n) - 1| < ε for infinitely
  many n (`MapClusterPt`). The ratio is taken in ℝ; it is only undefined (and is 0 in Lean)
  for n ≤ 1, where a(n) = 0, which does not affect a cluster point.
* Checked in Python: both definitions reproduce the listed terms of A038667 and A061057 for
  n ≤ 16.
-/

namespace OMA.S_oeis_a038667

open Filter

/-- A038667: `min |∏A - ∏B|` over partitions of `{1, ..., n}` into `A` and `B`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.image fun A : Finset ℕ =>
    ((∏ i ∈ A, (i : ℤ)) - ∏ i ∈ Finset.Icc 1 n \ A, (i : ℤ)).natAbs).min' (Finset.image_nonempty.mpr (Finset.powerset_nonempty _))

/-- A061057: `y - x` where `n! = x y`, `x ≤ y`, `x` maximal. -/
def A061057 (n : ℕ) : ℕ :=
  let x := ((Nat.factorial n).divisors.filter fun d => d * d ≤ Nat.factorial n).max' (by
    refine ⟨1, ?_⟩
    simp [Nat.one_le_iff_ne_zero, Nat.factorial_ne_zero])
  Nat.factorial n / x - x

/-- Peterson's conjecture: `1` is a limit point of `A061057(n)/a(n)`. -/
theorem main :
    MapClusterPt (1 : ℝ) atTop fun n : ℕ => (A061057 n : ℝ) / (a n : ℝ) := by
  sorry

end OMA.S_oeis_a038667
