import Mathlib

/-!
# Evasiveness (Aanderaa–Karp–Rosenberg) conjecture

Source: https://en.wikipedia.org/wiki/Aanderaa%E2%80%93Karp%E2%80%93Rosenberg_conjecture
Credit: @Solfanbtc

From the source: graphs are simple and undirected, and the only allowed primitive operation is
to test the adjacency of two vertices. A graph property maps graphs to `{0, 1}` so that
isomorphic graphs get the same value; it is non-trivial if it does not assign the same value to
all graphs, and monotone if the addition of edges does not destroy it. Richard Karp conjectured
that every nontrivial monotone graph property for graphs on `n` vertices is evasive, where a
property is evasive if determining whether a given graph has it sometimes requires all
`n (n - 1) / 2` possible queries.

Encoding: a deterministic algorithm that may only test adjacencies is a decision tree whose
inner nodes query a pair of distinct vertices and branch on the answer, and whose leaves give the
answer. Such a tree decides `P` if it answers `true` exactly on the graphs with `P`. "Sometimes
requires all possible queries" says that, on some graph, the tree tests every one of the
`n (n - 1) / 2` pairs of distinct vertices.
-/

namespace OMA.S_wpc_evasiveness_conjecture

/-- A query: an unordered pair of distinct vertices of `Fin n`. -/
abbrev Query (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- A deterministic decision tree querying elements of `α`: a leaf gives the answer, a node
queries `a` and continues in `no` or `yes` according to the answer. -/
inductive DecisionTree (α : Type) where
  | leaf : Bool → DecisionTree α
  | node : α → DecisionTree α → DecisionTree α → DecisionTree α

namespace DecisionTree

variable {α : Type}

/-- The answer of the tree on the input `x`. -/
def eval : DecisionTree α → (α → Bool) → Bool
  | leaf b, _ => b
  | node a no yes, x => if x a then eval yes x else eval no x

/-- The set of queries the tree makes on the input `x`. -/
def queried : DecisionTree α → (α → Bool) → Set α
  | leaf _, _ => ∅
  | node a no yes, x => insert a (if x a then queried yes x else queried no x)

end DecisionTree

open scoped Classical in
/-- The answers of a graph to the adjacency queries. -/
noncomputable def adjacency {n : ℕ} (G : SimpleGraph (Fin n)) : Query n → Bool :=
  fun e => decide (e.1 ∈ G.edgeSet)

/-- `P` is a graph property: isomorphic graphs on `n` vertices agree on it. -/
def IsGraphProperty {n : ℕ} (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ G H : SimpleGraph (Fin n), Nonempty (G ≃g H) → (P G ↔ P H)

/-- `P` is monotone: adding edges does not destroy it. -/
def IsMonotone {n : ℕ} (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ G H : SimpleGraph (Fin n), G ≤ H → P G → P H

/-- `P` is non-trivial: it does not assign the same value to all graphs on `n` vertices. -/
def IsNontrivial {n : ℕ} (P : SimpleGraph (Fin n) → Prop) : Prop :=
  (∃ G, P G) ∧ ∃ G, ¬ P G

/-- `P` is evasive: every decision tree that decides `P` tests, on some graph, all the
`n (n - 1) / 2` pairs of distinct vertices. -/
def IsEvasive {n : ℕ} (P : SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ T : DecisionTree (Query n), (∀ G, T.eval (adjacency G) = true ↔ P G) →
    ∃ G, T.queried (adjacency G) = Set.univ

/-- **Evasiveness conjecture** (Aanderaa–Karp–Rosenberg): every nontrivial monotone graph
property of graphs on `n` vertices is evasive. -/
theorem main : ∀ (n : ℕ) (P : SimpleGraph (Fin n) → Prop),
    IsGraphProperty P → IsMonotone P → IsNontrivial P → IsEvasive P := by
  sorry

end OMA.S_wpc_evasiveness_conjecture
