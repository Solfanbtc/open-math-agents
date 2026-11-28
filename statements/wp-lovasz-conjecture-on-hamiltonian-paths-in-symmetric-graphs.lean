import Mathlib

/-!
# Lovász conjecture on Hamiltonian paths in vertex-transitive graphs

Source: https://en.wikipedia.org/wiki/Lov%C3%A1sz_conjecture
Credit: @Solfanbtc

From the source: the Lovász conjecture (1969) says that every finite connected vertex-transitive
graph contains a Hamiltonian path. (László Babai published in 1996 a conjecture sharply
contradicting it; both remain open.)

Encoding: a finite graph is a `SimpleGraph` on a `Fintype`; it is vertex-transitive when its
automorphism group acts transitively on the vertices, that is, for any two vertices `u` and
`v` some automorphism `G ≃g G` sends `u` to `v`; a Hamiltonian path is a walk visiting
every vertex exactly once (`SimpleGraph.Walk.IsHamiltonian`).
-/

namespace OMA.S_wp_lovasz_conjecture_on_hamiltonian_paths_in_symmetric_graphs

/-- `G` is vertex-transitive: any vertex is sent to any other by an automorphism of `G`. -/
def IsVertexTransitive {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

/-- **Lovász conjecture**: every finite connected vertex-transitive graph contains a
Hamiltonian path. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → IsVertexTransitive G → ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  sorry

end OMA.S_wp_lovasz_conjecture_on_hamiltonian_paths_in_symmetric_graphs
