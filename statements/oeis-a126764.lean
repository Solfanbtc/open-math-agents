import Mathlib

/-!
# A126764: Number of L-convex polyominoes with n cells, that is, convex polyominoes where any two cells can be connected by a path internal t

Source: https://oeis.org/A126764
Credit: @Solfanbtc

OEIS A126764 counts *fixed* L-convex polyominoes with `n` cells (comment by A. C. Wechsler):
convex polyominoes in which any two cells are joined by a path inside the polyomino with at
most one change of direction. Offset 0, with `a(0) = 1` (the empty polyomino).

Conjecture (A. Guttmann and V. Kotesovec, Jun 09 2021, see also arXiv:2109.09928):
`a(n) ~ c * exp(π * sqrt(13 n / 6)) / n^(3/2)` with `c = 13 * sqrt 2 / 768`.

Model. A cell is a point of `ℕ × ℕ`. A fixed polyomino is counted up to translation by its unique
translate that meets both axes (some cell with first coordinate `0` and some cell with second
coordinate `0`); since it is connected, that translate lies in `[0, n) × [0, n)`.
`IsLConvex S` says: for any two cells `p, q ∈ S`, either the path from `p` horizontally to the
corner `(q.1, p.2)` and then vertically to `q` lies in `S`, or the path from `p` vertically to
`(p.1, q.2)` and then horizontally to `q` does. This implies connectedness and row/column
convexity (two cells in one row or column must be joined by the straight segment), so it is
exactly L-convexity. A brute-force enumeration of this definition gives
1, 1, 2, 6, 15, 35, 76, 156, 310, 590, 1098, 1984 for `n = 0..11`, matching the OEIS data.
-/

namespace OMA.S_oeis_a126764

/-- Any two cells of `S` are joined inside `S` by a path with at most one turn. -/
abbrev IsLConvex (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    ((∀ x ∈ Finset.Icc (min p.1 q.1) (max p.1 q.1), (x, p.2) ∈ S) ∧
      (∀ y ∈ Finset.Icc (min p.2 q.2) (max p.2 q.2), (q.1, y) ∈ S)) ∨
    ((∀ y ∈ Finset.Icc (min p.2 q.2) (max p.2 q.2), (p.1, y) ∈ S) ∧
      (∀ x ∈ Finset.Icc (min p.1 q.1) (max p.1 q.1), (x, q.2) ∈ S))

/-- `a n` = A126764(n): the number of fixed L-convex polyominoes with `n` cells. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).powerset.filter (fun S =>
    S.card = n ∧ (S.Nonempty → (∃ p ∈ S, p.1 = 0) ∧ (∃ p ∈ S, p.2 = 0)) ∧
      IsLConvex S)).card

/-- Guttmann–Kotesovec conjecture:
`A126764(n) ~ (13 √2 / 768) * exp(π √(13 n / 6)) / n^(3/2)`. -/
theorem main :
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => 13 * Real.sqrt 2 / 768 * Real.exp (Real.pi * Real.sqrt (13 * (n : ℝ) / 6)) /
        (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

end OMA.S_oeis_a126764
