import Mathlib

/-!
# A097391: The number of hierarchies of n labeled elements with at least one subhierarchy composed of exactly 2 levels and no subhierarchy with more than 2 levels.

Source: https://oeis.org/A097391
Credit: @Solfanbtc

Conjecture (Wouter Meeussen, Feb 10 2025): A097391 is A378854 / 3. Cross-reference A378854
(a(n) = number of solid partitions of n with 2 layers and second layer a plane partition of 2,
offset 4) whose comment says "Appears to equal 3*A097391(n-3)".

Index alignment. With the offsets of the two entries (A097391 from n = 1: 0, 1, 3, 8, 17, ...;
A378854 from n = 4: 3, 9, 24, 51, ...) the data match as A378854(n + 2) = 3 * A097391(n) for
n ≥ 2 (n = 2: 3 = 3*1, n = 3: 9 = 3*3, ..., n = 10: 1374 = 3*458). The shift "n-3" written in
A378854 does not match the data (it would give 9 = 3*1 at n = 5), so we state the conjecture
with the shift that the data of both entries support: `3 * a n = b (n + 2)` for `n ≥ 2`
(n ≥ 2 is where A378854(n + 2) is defined).

Definitions (following the entry's example, which counts unlabeled structures, as in
Sloane–Wieder, "The Number of Hierarchical Orderings", where a hierarchy is a multiset of
compositions):
* A hierarchy of n is a multiset of subhierarchies; a subhierarchy is a composition of a
  positive integer, its parts being the sizes of its levels (order of levels matters: 4|1 and
  1|4 are different; order of subhierarchies does not: 2|1:2 = 2:2|1). `a n` counts those of
  total size n in which every subhierarchy has at most 2 levels and at least one has exactly 2.
  This gives 0, 1, 3, 8, 17, 37, 71, 138, 252, 458 for n = 1..10, the data (python3).
  (The name says "labeled elements", but the data and the 17 hierarchies listed for n = 5
  are counted without labels, so the unlabeled count is the one that matches the source.)
* A plane partition is an array of naturals weakly decreasing along rows and columns; one of
  size at most n fits in an n × n box, so we use arrays `Fin n → Fin n → ℕ`. A solid partition
  with 2 layers is a pair of plane partitions (P1, P2) with P2 ≤ P1 entrywise and P2 ≠ 0;
  `b n` counts those with |P2| = 2 and |P1| + |P2| = n. This gives 3, 9, 24, 51, ... for
  n = 4, 5, 6, 7, ..., the data of A378854 (python3, brute force up to n = 16, matching the
  entry's examples for n = 4, 5).
* Checked with python3: 3 * a n = b (n + 2) for 1 ≤ n ≤ 14.
Both counts are `Set.ncard` of finite sets.
-/

namespace OMA.S_oeis_a097391

/-- `s` is a hierarchy of `n` with at least one subhierarchy of exactly 2 levels and none with
more than 2 levels. A subhierarchy is a composition `c.2` of `c.1 > 0`. -/
def IsHier (n : ℕ) (s : Multiset (Σ k : ℕ, Composition k)) : Prop :=
  (s.map Sigma.fst).sum = n ∧ (∀ c ∈ s, 0 < c.1 ∧ c.2.length ≤ 2) ∧
    ∃ c ∈ s, c.2.length = 2

/-- A097391(n). -/
noncomputable def a (n : ℕ) : ℕ := {s : Multiset (Σ k : ℕ, Composition k) | IsHier n s}.ncard

/-- `f` is a plane partition (in an `m × m` box): weakly decreasing along rows and columns. -/
def IsPlanePartition {m : ℕ} (f : Fin m → Fin m → ℕ) : Prop :=
  (∀ i i' j, i ≤ i' → f i' j ≤ f i j) ∧ (∀ i j j', j ≤ j' → f i j' ≤ f i j)

/-- The size (sum of entries) of an array. -/
def size {m : ℕ} (f : Fin m → Fin m → ℕ) : ℕ := ∑ i, ∑ j, f i j

/-- A378854(n): solid partitions of `n` with 2 layers `P1 ≥ P2`, the second layer `P2` a plane
partition of 2. -/
noncomputable def b (n : ℕ) : ℕ :=
  {p : (Fin n → Fin n → ℕ) × (Fin n → Fin n → ℕ) |
    IsPlanePartition p.1 ∧ IsPlanePartition p.2 ∧ (∀ i j, p.2 i j ≤ p.1 i j) ∧
      size p.2 = 2 ∧ size p.1 + size p.2 = n}.ncard

theorem main : ∀ n : ℕ, 2 ≤ n → 3 * a n = b (n + 2) := by
  sorry

end OMA.S_oeis_a097391
