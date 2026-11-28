import Mathlib

/-!
# A140462: Turan's upper bound on the number of triangles of a simplicial complex of dimension two for which every minimal non-face has three vertices.

Source: https://oeis.org/A140462
Credit: @Solfanbtc

The entry gives (%F)
  a(n) = (5/2) k^3 - (3/2) k^2          if n = 3k,
  a(n) = (5/2) k^3 + k^2 - (1/2) k       if n = 3k + 1,
  a(n) = (5/2) k^3 + (7/2) k^2 + k       if n = 3k + 2,
and the conjecture (Turán's (3,4)-conjecture, Conjecture 1.2 of Frohmader, see also Erdős problem
#500) is that `a(n)` is an upper bound: every simplicial complex of dimension two on `n` vertices
for which every minimal non-face has three vertices has at most `a(n)` triangles.

Formalization:
* A simplicial complex on the vertex set `Fin n` is a family `F` of finite subsets (its faces)
  closed under taking subsets. "Of dimension two" is: every face has at most `3` vertices
  (allowing dimension `< 2` only adds complexes with no triangle, for which the bound is trivial).
* A minimal non-face is a set `S ∉ F` all of whose subsets `S.erase x` (`x ∈ S`) are faces
  (for a family closed under subsets this is the usual inclusion-minimality). The hypothesis says
  every such `S` has exactly `3` elements. In particular `∅`, every vertex and every pair are faces,
  so the complex has exactly the `n` vertices of `Fin n`.
* The triangles are the faces with `3` vertices. The bound `a(n)` is taken literally from the
  formula, in `ℚ`, with `k = n / 3` (it is always an integer).
Equivalently the triangles form a `3`-uniform hypergraph on `n` vertices with no `K_4^{(3)}`.
For `n ≤ 6` an exhaustive search over such hypergraphs gives maxima `0, 0, 0, 1, 3, 7, 14`, equal
to `a(n)`, so the bound is attained there.
-/

namespace OMA.S_oeis_a140462

/-- A140462, from the formula in the entry, with `k = ⌊n/3⌋`. -/
def a (n : ℕ) : ℚ :=
  let k : ℚ := (n / 3 : ℕ)
  if n % 3 = 0 then 5 / 2 * k ^ 3 - 3 / 2 * k ^ 2
  else if n % 3 = 1 then 5 / 2 * k ^ 3 + k ^ 2 - 1 / 2 * k
  else 5 / 2 * k ^ 3 + 7 / 2 * k ^ 2 + k

/-- Turán's conjecture: a two-dimensional simplicial complex on `n` vertices all of whose
minimal non-faces have three vertices has at most `a(n)` triangles. -/
theorem main : ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    (∀ s ∈ F, ∀ t, t ⊆ s → t ∈ F) →
    (∀ s ∈ F, s.card ≤ 3) →
    (∀ S : Finset (Fin n), S ∉ F → (∀ x ∈ S, S.erase x ∈ F) → S.card = 3) →
    ((F.filter (fun s => s.card = 3)).card : ℚ) ≤ a n := by
  sorry

end OMA.S_oeis_a140462
