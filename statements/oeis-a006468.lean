import Mathlib

/-!
# A006468: Number of rooted planar maps with 4 faces and n vertices and no isthmuses

Source: https://oeis.org/A006468
Credit: @Solfanbtc

Claim (OEIS formula): the g.f. is `-x (x^3 - 4x^2 + 2x + 5)/(x - 1)^7`, equivalently
`a(n) = n (n+1) (n+2) (2n^3 + 33n^2 + 142n + 123) / 360` for `n ≥ 1` (offset 1), conjectured in
Simon Plouffe's Master's thesis (1992).

Status: SOLVED. The OEIS entry says "The above conjecture is true" (Andrew Howroyd, Apr 02 2021;
A006468 is column `k = 4` of A342981). It is stated here faithfully as the closed form, written
without division as `360 a(n) = n (n+1) (n+2) (2n^3 + 33n^2 + 142n + 123)`; it agrees with all
35 data terms `5, 37, 150, 449, …, 16999206`.

Model (combinatorial maps). A map with `E` edges is a pair `(σ, α)` of permutations of the
`2E` darts `Fin (2E)`, where `α` is a fixed-point-free involution (the edges), `σ` gives the
rotation at each vertex (vertices = cycles of `σ`, fixed points included) and the faces are the
cycles of `σ * α` (`α` first); the map is connected iff `⟨σ, α⟩` acts transitively. A connected
map with `V` vertices, `E` edges and `F` faces is planar (genus 0) iff `V - E + F = 2`, so a
planar map with `4` faces and `n` vertices has `E = n + 2` edges, and conversely every connected
map with these numbers is planar. An edge `{d, α d}` is an isthmus (bridge) iff the faces on its
two sides coincide, i.e. `d` and `α d` lie in the same cycle of `σ * α` (for planar maps this is
equivalent to the edge being a bridge of the underlying graph: an edge is a bridge iff it is a
loop of the dual map). Rooted maps have trivial automorphism group, so the conjugation action of
`Perm (Fin (2E))` on labelled maps has orbits of size `(2E)! / |Aut|`, and the number of rooted
maps (a map together with a root dart, up to isomorphism) is the number of labelled maps divided
by `(2E - 1)!` (the division is exact). With this model a brute-force count gives `5` for `n = 1`
(`600 / 5!`) and `37` for `n = 2` (`186480 / 7!`), as in the sequence.
-/

namespace OMA.S_oeis_a006468

open Equiv

/-- Number of cycles of a permutation of `Fin N`, fixed points included. -/
noncomputable def numCycles {N : ℕ} (p : Perm (Fin N)) : ℕ :=
  Nat.card (Quotient (Perm.SameCycle.setoid p))

/-- `(σ, α)` is a labelled connected map on the darts `Fin (2E)` with `V` vertices and `F` faces
and no isthmus. -/
def IsMapNoIsthmus (E V F : ℕ) (p : Perm (Fin (2 * E)) × Perm (Fin (2 * E))) : Prop :=
  (∀ d, p.2 d ≠ d) ∧ (∀ d, p.2 (p.2 d) = d) ∧
  (∀ d d', ∃ g ∈ Subgroup.closure ({p.1, p.2} : Set (Perm (Fin (2 * E)))), g d = d') ∧
  numCycles p.1 = V ∧ numCycles (p.1 * p.2) = F ∧
  ∀ d, ¬ (p.1 * p.2).SameCycle d (p.2 d)

/-- A006468: rooted planar maps with 4 faces, `n` vertices (hence `n + 2` edges) and no
isthmuses: labelled such maps divided by `(2E - 1)!`, `E = n + 2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p // IsMapNoIsthmus (n + 2) n 4 p} / (2 * (n + 2) - 1).factorial

/-- Plouffe's conjecture (proved, see the module docstring):
`a(n) = n (n+1) (n+2) (2n^3 + 33n^2 + 142n + 123) / 360` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    360 * a n = n * (n + 1) * (n + 2) * (2 * n ^ 3 + 33 * n ^ 2 + 142 * n + 123) := by
  sorry

end OMA.S_oeis_a006468
