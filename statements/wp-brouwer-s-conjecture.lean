import Mathlib

/-!
# Brouwer's conjecture

Source: https://en.wikipedia.org/wiki/Brouwer%27s_conjecture
Credit: @Solfanbtc

From the source: Brouwer's conjecture, in spectral graph theory, states that if `G` is a simple
undirected graph and `L(G)` its Laplacian matrix, then its eigenvalues
`λ_n(L(G)) ≤ λ_{n-1}(L(G)) ≤ ⋯ ≤ λ_1(L(G))` satisfy
`∑_{i=1}^{t} λ_i(L(G)) ≤ m(G) + (t + 1).choose 2` for `t = 1, …, n`, where `m(G)` is the number of
edges of `G`. It has been verified for all graphs with at most 11 vertices, and for every number
of vertices when `t = 1, 2, 3, n - 4, n - 3, n - 2, n - 1, n`.

Encoding: `G` is a `SimpleGraph` on a finite type with `n = Fintype.card V` vertices, `L(G)` is
Mathlib's `SimpleGraph.lapMatrix ℝ G` (degree matrix minus adjacency matrix), which is Hermitian,
and `Matrix.IsHermitian.eigenvalues₀` lists its eigenvalues in decreasing order (it is
antitone), so `λ_i` with `1 ≤ i ≤ n` is `eigenvalues₀ ⟨i - 1, _⟩` and the sum of the `t` largest
eigenvalues is the sum of `eigenvalues₀ j` over the indices `j < t`.
-/

namespace OMA.S_wp_brouwer_s_conjecture

/-- The sum `λ_1 + ⋯ + λ_t` of the `t` largest eigenvalues of the Laplacian of `G`. -/
noncomputable def topLaplacianSum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card V) => (j : ℕ) < t),
    (G.isHermitian_lapMatrix ℝ).eigenvalues₀ j

/-- **Brouwer's conjecture**: for every simple graph `G` on `n` vertices with `m` edges and every
`t = 1, …, n`, the sum of the `t` largest Laplacian eigenvalues of `G` is at most
`m + (t + 1).choose 2`. -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : ℕ), 1 ≤ t → t ≤ Fintype.card V →
      topLaplacianSum G t ≤ (G.edgeFinset.card : ℝ) + ((t + 1).choose 2 : ℕ) := by
  sorry

end OMA.S_wp_brouwer_s_conjecture
