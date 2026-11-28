import Mathlib

/-!
# A139250: The toothpick sequence (see Comments lines for definition).

Source: https://oeis.org/A139250
Credit: @Solfanbtc

Conjecture (OEIS A139250, comment): consider the rectangles in the sieve (including the
squares). The area of each rectangle (A = b*c) and the edges (b and c) are powers of 2,
but at least one of the edges (b or c) is <= 2.

Modelling choices, following the definition in the entry:
* A toothpick is a copy of `[-1, 1]`, so it has length 2 in grid units; this is the unit
  in which the edges b, c are measured (the comments of the entry on the "bar chart"
  substructure give regions of width 2 with heights 1, 2, 1, 4, ..., in this unit).
* Stage 1 is one vertical toothpick centred at the origin; at each later stage a new
  toothpick, perpendicular to its parent, is centred at every exposed endpoint (an endpoint
  touching no other toothpick), which is the growth rule as restated in the entry. All
  toothpicks lie on grid lines with integer endpoints and midpoints, so two of them touch
  iff they share a lattice point. A toothpick is `(c, v)`: midpoint `c`, vertical iff `v`.
  With this rule the number of toothpicks after n stages is the sequence of the entry
  (checked by a simulation for n <= 40).
* The sieve is the complement of the union of the toothpicks. Since toothpicks are unions
  of unit grid edges, its regions are unions of unit cells: the cell `(i, j)` is the square
  `[i, i+1] x [j, j+1]`, and two side-adjacent cells lie in the same region iff their
  common unit edge is not covered by a toothpick. The closed regions (holes) of the sieve
  are the finite connected components of this cell graph.
* A region is a rectangle with edges b (horizontal) and c (vertical) iff its set of cells
  is `[a, a+b) x [d, d+c)` for some integers a, d. The source does not say at which stage
  the sieve is taken; the statement covers the sieve after every stage n. (A simulation up
  to stage 40 finds every hole to be such a rectangle, with edges as claimed.) The area
  b*c is then a power of 2 automatically.
-/

namespace OMA.S_oeis_a139250

/-- A toothpick: its midpoint and whether it is vertical. -/
abbrev Toothpick := (ℤ × ℤ) × Bool

/-- The two endpoints of a toothpick of length 2. -/
def endpoints (t : Toothpick) : Finset (ℤ × ℤ) :=
  if t.2 then {(t.1.1, t.1.2 - 1), (t.1.1, t.1.2 + 1)}
  else {(t.1.1 - 1, t.1.2), (t.1.1 + 1, t.1.2)}

/-- The lattice points lying on a toothpick. -/
def points (t : Toothpick) : Finset (ℤ × ℤ) := insert t.1 (endpoints t)

/-- One stage of growth: a perpendicular toothpick is centred at every exposed endpoint,
an endpoint of a toothpick of `S` that lies on no other toothpick of `S`. -/
def step (S : Finset Toothpick) : Finset Toothpick :=
  S ∪ S.biUnion (fun t => ((endpoints t).filter
    (fun p => ∀ t' ∈ S, t' ≠ t → p ∉ points t')).image (fun p => (p, !t.2)))

/-- The toothpick structure after `n` stages (none at stage 0, one vertical at stage 1). -/
def config : ℕ → Finset Toothpick
  | 0 => ∅
  | n + 1 => step^[n] {((0, 0), true)}

/-- The vertical unit edge from `(x, y)` to `(x, y+1)` lies on a toothpick of `S`. -/
def vBlocked (S : Finset Toothpick) (x y : ℤ) : Prop :=
  ((x, y), true) ∈ S ∨ ((x, y + 1), true) ∈ S

/-- The horizontal unit edge from `(x, y)` to `(x+1, y)` lies on a toothpick of `S`. -/
def hBlocked (S : Finset Toothpick) (x y : ℤ) : Prop :=
  ((x, y), false) ∈ S ∨ ((x + 1, y), false) ∈ S

/-- Cells `(i, j)` (the unit square `[i, i+1] x [j, j+1]`), adjacent when they share a side
not covered by a toothpick of `S`. -/
def cellGraph (S : Finset Toothpick) : SimpleGraph (ℤ × ℤ) :=
  SimpleGraph.fromRel fun p q =>
    (q = (p.1 + 1, p.2) ∧ ¬ vBlocked S (p.1 + 1) p.2) ∨
    (q = (p.1, p.2 + 1) ∧ ¬ hBlocked S p.1 (p.2 + 1))

/-- Conjecture: after any number of stages, every closed region of the toothpick sieve that
is a rectangle with horizontal edge `b` and vertical edge `c` has `b` and `c` (hence also
its area `b * c`) powers of 2, and `b ≤ 2` or `c ≤ 2`. -/
theorem main : ∀ n : ℕ, ∀ C : (cellGraph (config n)).ConnectedComponent,
    C.supp.Finite →
    ∀ a d : ℤ, ∀ b c : ℕ,
      C.supp = {p : ℤ × ℤ | a ≤ p.1 ∧ p.1 < a + b ∧ d ≤ p.2 ∧ p.2 < d + c} →
      (∃ i : ℕ, b = 2 ^ i) ∧ (∃ j : ℕ, c = 2 ^ j) ∧ (∃ k : ℕ, b * c = 2 ^ k) ∧
        (b ≤ 2 ∨ c ≤ 2) := by
  sorry

end OMA.S_oeis_a139250
