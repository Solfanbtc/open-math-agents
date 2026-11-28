import Mathlib

/-!
# A033487: a(n) = n*(n+1)*(n+2)*(n+3)/4.

Source: https://oeis.org/A033487
Credit: @Solfanbtc

Conjecture (Eric W. Weisstein, Apr 29 2019): `a(n)` is the crossing number of the
`(n+3)`-cocktail party graph, i.e. `cr(CP(n+3)) = n(n+1)(n+2)(n+3)/4` for all `n ≥ 0`.

Formalized:
* The `m`-cocktail party graph (MathWorld) has `2m` vertices `Fin m × Fin 2`, two vertices
  being adjacent iff they are not in the same pair: the complete `m`-partite graph `K_{m×2}`,
  i.e. `K_{2m}` minus a perfect matching. `CP(3)` is the octahedron (planar, `a(0) = 0`).
* Drawings are good drawings, as in the merged statement
  `statements/opg-the-crossing-number-of-the-complete-bipartite-graph.lean`: vertices are distinct
  points of the plane, each edge is an arc (continuous injective image of `[0,1]`) joining the
  images of its endpoints, (1) no edge passes through a vertex other than its endpoints,
  (2) adjacent edges share only their common endpoint, (3) nonadjacent edges share at most one
  point, (4) no non-vertex point lies on three edges. The number of crossings is the number of
  unordered pairs of nonadjacent edges that meet, and `cr` is its minimum over all drawings.
  Restricting to good drawings does not change the minimum (a standard fact: every drawing with
  the minimum number of crossings can be taken good), and every finite graph has such a drawing,
  so the infimum is attained.
* `n*(n+1)*(n+2)*(n+3)/4` is an exact natural-number quotient (`= 6 * C(n+3, 4)`).
-/

namespace OMA.S_oeis_a033487

open Classical

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The `m`-cocktail party graph `K_{m×2}` on the vertices `Fin m × Fin 2`. -/
def cocktail (m : ℕ) : SimpleGraph (Fin m × Fin 2) where
  Adj x y := x.1 ≠ y.1
  symm := ⟨fun _ _ h => Ne.symm h⟩
  loopless := ⟨fun _ h => h rfl⟩

/-- A good drawing of a simple graph `G` in the plane. -/
structure Drawing {V : Type} (G : SimpleGraph V) where
  pos : V → Plane
  pos_inj : Function.Injective pos
  arc : G.edgeSet → unitInterval → Plane
  arc_cont : ∀ e : G.edgeSet, Continuous (arc e)
  arc_inj : ∀ e : G.edgeSet, Function.Injective (arc e)
  /-- the arc of `e = s(u, v)` joins `pos u` and `pos v` -/
  arc_ends : ∀ e : G.edgeSet, Sym2.map pos (e : Sym2 V) = s(arc e 0, arc e 1)
  /-- (1) no edge contains a vertex other than its endpoints -/
  no_vertex : ∀ (e : G.edgeSet) (v : V), v ∉ (e : Sym2 V) → pos v ∉ Set.range (arc e)
  /-- (2) adjacent edges share only their common endpoint -/
  adjacent_meet : ∀ e e' : G.edgeSet, e ≠ e' → ∀ v, v ∈ (e : Sym2 V) → v ∈ (e' : Sym2 V) →
    Set.range (arc e) ∩ Set.range (arc e') = {pos v}
  /-- (3) nonadjacent edges share at most one point -/
  nonadjacent_meet : ∀ e e' : G.edgeSet, (∀ v, v ∈ (e : Sym2 V) → v ∉ (e' : Sym2 V)) →
    (Set.range (arc e) ∩ Set.range (arc e')).Subsingleton
  /-- (4) no three edges through a common non-vertex point -/
  no_triple : ∀ p : Plane, p ∉ Set.range pos → ∀ e₁ e₂ e₃ : G.edgeSet,
    p ∈ Set.range (arc e₁) → p ∈ Set.range (arc e₂) → p ∈ Set.range (arc e₃) →
    e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃

/-- Number of crossings of a drawing: unordered pairs of nonadjacent edges that meet
(ordered pairs are counted, then halved; the relation is symmetric and irreflexive). -/
noncomputable def Drawing.crossings {V : Type} [Fintype V] {G : SimpleGraph V}
    (D : Drawing G) : ℕ :=
  (Finset.univ.filter fun p : G.edgeSet × G.edgeSet =>
    (∀ v, v ∈ (p.1 : Sym2 V) → v ∉ (p.2 : Sym2 V)) ∧
      (Set.range (D.arc p.1) ∩ Set.range (D.arc p.2)).Nonempty).card / 2

/-- The crossing number of a finite simple graph. -/
noncomputable def crossingNumber {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf (Set.range (Drawing.crossings (G := G)))

theorem main : ∀ n : ℕ,
    crossingNumber (cocktail (n + 3)) = n * (n + 1) * (n + 2) * (n + 3) / 4 := by
  sorry

end OMA.S_oeis_a033487
