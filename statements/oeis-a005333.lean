import Mathlib

/-!
# A005333: 2-colored connected labeled graphs with n vertices of each color

Source: https://oeis.org/A005333
Credit: @Solfanbtc

Conjecture (Lorenzo Sauras Altuzarra, Sep 17 2022, in the entry): if `n > 1`, then `a(n)` is
the number of labeled digraphs `D` (allowing self-loops) with `n` vertices such that `D|D'` and
`D'|D` are (strongly) connected (see the preliminaries of Broere et al.).

Conventions:
* `a(n)` (offset 1) counts the labeled bipartite graphs on two disjoint color classes
  `Fin n ⊕ Fin n` (every edge joins the two classes) that are connected. A 2-colored graph with
  `n` vertices of each color, edges only between colors, is exactly a relation
  `Fin n → Fin n → Prop` (which first-color vertex is joined to which second-color vertex).
* A labeled digraph allowing self-loops on `n` vertices is a relation `D : Fin n → Fin n → Prop`.
  `D'` is the converse digraph (`D' i j ↔ D j i`) and `D|D'` is the relational composition
  (`(D|D') i j ↔ ∃ k, D i k ∧ D' k j`), as in relation algebra (Broere et al. use relational
  notation). A digraph is strongly connected when every vertex reaches every vertex by a
  directed walk (`Relation.ReflTransGen`); for one vertex this always holds.
* Under this reading a brute-force Python check gives `5, 205, 36317` for `n = 2, 3, 4`,
  matching the data, and `2 ≠ a(1) = 1` at `n = 1`, which is why the comment requires `n > 1`.
-/

namespace OMA.S_oeis_a005333

/-- The bipartite graph on `Fin n ⊕ Fin n` with first-color vertex `i` joined to second-color
vertex `j` exactly when `E i j`. -/
def bipartiteOf {n : ℕ} (E : Fin n → Fin n → Prop) : SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ i j, u = Sum.inl i ∧ v = Sum.inr j ∧ E i j

/-- OEIS A005333: connected 2-colored labeled graphs with `n` vertices of each color. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {E : Fin n → Fin n → Prop // (bipartiteOf E).Connected}

/-- Relational composition `D|D''`: `i → j` iff `i → k` in `D` and `k → j` in `D''` for some `k`. -/
def comp {n : ℕ} (D D'' : Fin n → Fin n → Prop) : Fin n → Fin n → Prop :=
  fun i j => ∃ k, D i k ∧ D'' k j

/-- The converse digraph `D'`. -/
def conv {n : ℕ} (D : Fin n → Fin n → Prop) : Fin n → Fin n → Prop :=
  fun i j => D j i

/-- Strong connectivity: every vertex reaches every vertex along arcs of `R`. -/
def StronglyConnected {n : ℕ} (R : Fin n → Fin n → Prop) : Prop :=
  ∀ i j, Relation.ReflTransGen R i j

/-- Sauras Altuzarra's conjecture: for `n > 1`, `a(n)` counts the digraphs `D` with loops on
`n` labeled vertices such that `D|D'` and `D'|D` are strongly connected. -/
theorem main : ∀ n : ℕ, 1 < n →
    Nat.card {D : Fin n → Fin n → Prop //
      StronglyConnected (comp D (conv D)) ∧ StronglyConnected (comp (conv D) D)} = a n := by
  sorry

end OMA.S_oeis_a005333
