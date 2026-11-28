import Mathlib

/-!
# A045831: Number of 4-core partitions of n.

Source: https://oeis.org/A045831
Credit: @Solfanbtc

Conjecture (Fred Lunnon, OEIS A045831, comment, Mar 05 2015): conjecturally
Sum_n a(n) q^(8n+5) equals the theta series of sodalite ("the sodalite net, aka edge-skeleton
of space honeycomb by truncated octahedra", example section of the entry).

Conventions:
* a(n) is the number of partitions of n that are 4-cores, i.e. that have no hook length
  divisible by 4 (the standard definition of a t-core). The hook length of the cell (i, j)
  (0-indexed, j < λ_i) of a partition λ_0 ≥ λ_1 ≥ ... is λ_i - j + λ'_j - i - 1, where
  λ'_j = #{i | λ_i > j}.
* The sodalite net is the vertex set of the space-filling by truncated octahedra (the
  bitruncated cubic honeycomb), in its standard coordinates: the truncated octahedron centred
  at c has the 24 vertices c + w, with w running over the vectors whose coordinates are a
  permutation of (0, ±1, ±2); the centres c run over the body-centred cubic lattice
  4ℤ³ ∪ ((2,2,2) + 4ℤ³). The theta series is Sum_v q^(|v|²), centred at the origin (a cell
  centre); in these coordinates the squared norms are 5, 13, 21, ..., matching the exponents
  8n+5 of the conjecture.
* Minimal fix (normalization): taken literally, the coefficient of q^5 in the theta series is
  24 (the 24 vertices (0, ±1, ±2) up to permutation), not a(0) = 1. A Python count of the
  vertices in the box [-30, 30]³ gives 24, 24, 48, 72, 24, 72, 72, 72, 96, 96, ... vertices of
  squared norm 8n+5 for n = 0..19, exactly 24 a(n), and no vertex of any other squared norm.
  So the statement is: every vertex has squared norm ≡ 5 (mod 8), and for every n the number
  of vertices of squared norm 8n+5 is 24 a(n), i.e. the theta series is 24 Sum_n a(n) q^(8n+5)
  (it equals Sum_n a(n) q^(8n+5) after dividing by the 24 vertices of one cell).
-/

namespace OMA.S_oeis_a045831

/-- The hook length of the cell `(i, j)` of the partition with parts `l` (in decreasing order). -/
def hook (l : List ℕ) (i j : ℕ) : ℕ :=
  l.getD i 0 - j + (l.filter fun x => j < x).length - i - 1

/-- A partition (given by its parts in decreasing order) is a `t`-core: no hook length of a
cell of its Young diagram is divisible by `t`. -/
def IsCore (t : ℕ) (l : List ℕ) : Prop :=
  ∀ i < l.length, ∀ j < l.getD i 0, ¬ t ∣ hook l i j

/-- A045831: the number of 4-core partitions of `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // IsCore 4 (p.parts.sort (· ≥ ·))}

/-- A vertex of a truncated octahedron centred at the origin: the coordinates are a permutation
of `(0, ±1, ±2)`, i.e. their absolute values are `0, 1, 2` in some order. -/
def IsCellVertex (w : ℤ × ℤ × ℤ) : Prop :=
  ({w.1.natAbs, w.2.1.natAbs, w.2.2.natAbs} : Multiset ℕ) = {0, 1, 2}

/-- The body-centred cubic lattice of cell centres `4ℤ³ ∪ ((2,2,2) + 4ℤ³)`. -/
def IsCentre (c : ℤ × ℤ × ℤ) : Prop :=
  (4 ∣ c.1 ∧ 4 ∣ c.2.1 ∧ 4 ∣ c.2.2) ∨ (4 ∣ c.1 - 2 ∧ 4 ∣ c.2.1 - 2 ∧ 4 ∣ c.2.2 - 2)

/-- The sodalite net: the vertices of the honeycomb by truncated octahedra. -/
def Sodalite : Set (ℤ × ℤ × ℤ) :=
  {v | ∃ c, IsCentre c ∧ IsCellVertex (v - c)}

/-- The squared Euclidean norm. -/
def normSq (v : ℤ × ℤ × ℤ) : ℤ := v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

/-- Lunnon's conjecture: the theta series of sodalite is `24 Sum_n a(n) q^(8n+5)`. -/
theorem main :
    (∀ v ∈ Sodalite, normSq v % 8 = 5) ∧
    (∀ n : ℕ, Nat.card {v // v ∈ Sodalite ∧ normSq v = 8 * n + 5} = 24 * a n) := by
  sorry

end OMA.S_oeis_a045831
