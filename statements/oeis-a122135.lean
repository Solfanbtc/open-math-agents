import Mathlib

/-!
# A122135: Expansion of f(x, -x^4) / phi(-x^2) in powers of x where f(, ) and phi() are Ramanujan theta functions.

Source: https://oeis.org/A122135
Credit: @Solfanbtc

Conjectures (Gus Wiseman, OEIS A122135, comments, Feb 26 2022):
1. a(n) is also the number of integer partitions y of n such that y_i > y_{i+1} for all even i.
2. The even-length case (partitions as in 1 with an even number of parts) appears to be
   A122134, the expansion of Sum_{k>=0} x^(k^2+k)/((1-x)(1-x^2)...(1-x^(2k))).
`main` is the conjunction of 1 and 2.
Status: per a comment of Peter Bala (Jan 02 2025), conjecture 1 (with three other
partition-theoretic interpretations) is proved in W. G. Connor, Partition theorems related to
some identities of Rogers and Watson, Trans. Amer. Math. Soc. 214 (1975), 95-111,
Proposition 4. It is still stated here as recorded in the entry.

Conventions:
* a(n) is defined by the g.f. of %F, Sum_{k>=0} x^(k^2+k) / ((1-x)(1-x^2)...(1-x^(2k+1))),
  whose coefficient of x^n is `Σ_k p(n - k(k+1), parts ≤ 2k+1)`. A122134 is the same with
  parts `≤ 2k` (its %N). (`partsAtMost m M` = number of partitions of `m` into parts `≤ M`; the
  index `k ≤ n` is enough since `k(k+1) ≤ n`.)
* A partition y = (y_1 ≥ y_2 ≥ ...) is its multiset of parts sorted in decreasing order; the
  condition "y_i > y_{i+1} for all even i" (1-indexed, whenever y_{i+1} exists) is, 0-indexed,
  `l[i] > l[i+1]` for every odd `i` with `i + 1 < length`.
* Checked in Python: the g.f. coefficients reproduce every term of %S, %T, %U of A122135 and
  of A122134; both partition counts agree for n < 30.
-/

namespace OMA.S_oeis_a122135

/-- Number of partitions of `m` with all parts at most `M`. -/
def partsAtMost (m M : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition m)).filter fun μ => ∀ i ∈ μ.parts, i ≤ M).card

/-- A122135 via `Σ_k x^(k^2+k) / ((1-x)...(1-x^(2k+1)))`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * k + k ≤ n),
    partsAtMost (n - (k * k + k)) (2 * k + 1)

/-- A122134: `Σ_k x^(k^2+k) / ((1-x)...(1-x^(2k)))`. -/
def A122134 (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * k + k ≤ n),
    partsAtMost (n - (k * k + k)) (2 * k)

/-- The parts of `μ` in decreasing order. -/
def desc {n : ℕ} (μ : Nat.Partition n) : List ℕ := μ.parts.sort (· ≥ ·)

/-- `y_i > y_{i+1}` for every even (1-indexed) `i`. -/
def StrictAtEven (l : List ℕ) : Prop :=
  ∀ i < l.length - 1, i % 2 = 1 → l.getD (i + 1) 0 < l.getD i 0

instance : DecidablePred StrictAtEven := fun l => by unfold StrictAtEven; infer_instance

/-- Wiseman's two conjectures. -/
theorem main :
    (∀ n : ℕ, ((Finset.univ : Finset (Nat.Partition n)).filter fun μ =>
        StrictAtEven (desc μ)).card = a n) ∧
    (∀ n : ℕ, ((Finset.univ : Finset (Nat.Partition n)).filter fun μ =>
        StrictAtEven (desc μ) ∧ Even (desc μ).length).card = A122134 n) := by
  sorry

end OMA.S_oeis_a122135
