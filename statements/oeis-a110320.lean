import Mathlib

/-!
# A110320: Number of blocks in all RNA secondary structures with n nodes.

Source: https://oeis.org/A110320
Credit: @Solfanbtc

Conjecture (Gerald McGarvey, Jan 14 2007, in the entry): a(n) = (A051292(n+2) - A051286(n+1))/2.

Conventions.
* An RNA secondary structure on nodes 0..n-1 (viewed as a restricted noncrossing partition) is
  a set of arcs (i, j), i < j, with j - i ≥ 2, each node in at most one arc, and no two arcs
  crossing (i < k < j < l). Its blocks are the arcs and the unpaired nodes, so it has
  n - #arcs blocks. a(n) (offset 1) is the total number of blocks over all structures. (Entry
  example: n = 4 has the 4 structures 1/2/3/4, 13/2/4, 14/2/3, 1/24/3 with 13 blocks.)
  python3: 1, 2, 5, 13, 32, 80, 201, 505, ... (first 12 terms of the data).
* A051286(n) = Whitney number of level n of the lattice of ideals of the fence of order 2n, and
  A051292(n) = the same for the crown of size 2n: the number of ideals (down-sets) with n
  elements. Both posets have elements 0..2n-1, even elements minimal and odd elements maximal;
  in the fence each odd j covers j-1 and j+1 (when j+1 < 2n); in the crown, additionally,
  2n-1 covers 0 (cyclically). Brute force (python3): fence gives 1, 2, 5, 11, 26, 63, 153 for
  n = 1..7 (A051286), crown gives 1, 4, 9, 21, 52, 127 for n = 2..7 (A051292). Only
  A051286(m) for m ≥ 2 and A051292(m) for m ≥ 3 are used, where these posets are as described.
* Stated without division: 2 a(n) = A051292(n+2) - A051286(n+1) for n ≥ 1 (python3: holds for
  n = 1..12 on the data).
-/

namespace OMA.S_oeis_a110320

/-- RNA secondary structures on n nodes, as sets of arcs. -/
def IsRNA {n : ℕ} (A : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ A, p.1.val + 2 ≤ p.2.val) ∧
  (∀ p ∈ A, ∀ q ∈ A, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
  (∀ p ∈ A, ∀ q ∈ A, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))

open scoped Classical in
/-- A110320: total number of blocks over all RNA secondary structures on n nodes. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ A ∈ (Finset.univ : Finset (Finset (Fin n × Fin n))).filter (fun A => IsRNA A), (n - A.card)

/-- Lower covers of the maximal element j (odd) in the fence (cyclic = false) or crown
(cyclic = true) on 2n elements. -/
def Covers (m : ℕ) (cyclic : Bool) (i j : ℕ) : Prop :=
  j % 2 = 1 ∧ (i + 1 = j ∨ i = j + 1 ∨ (cyclic = true ∧ j + 1 = m ∧ i = 0))

open scoped Classical in
/-- Number of ideals of size `level` of the fence / crown on m elements. -/
noncomputable def idealsOfSize (m : ℕ) (cyclic : Bool) (level : ℕ) : ℕ :=
  ((Finset.range m).powersetCard level |>.filter fun S =>
    ∀ j ∈ S, ∀ i < m, Covers m cyclic i j → i ∈ S).card

/-- A051286: Whitney number of level n of the ideal lattice of the fence of order 2n. -/
noncomputable def A051286 (n : ℕ) : ℕ := idealsOfSize (2 * n) false n

/-- A051292: Whitney number of level n of the ideal lattice of the crown of size 2n. -/
noncomputable def A051292 (n : ℕ) : ℕ := idealsOfSize (2 * n) true n

theorem main : ∀ n : ℕ, 1 ≤ n →
    2 * (a n : ℤ) = (A051292 (n + 2) : ℤ) - A051286 (n + 1) := by
  sorry

end OMA.S_oeis_a110320
