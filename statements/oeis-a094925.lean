import Mathlib

/-!
# A094925: A hexagonal spiral Fibonacci sequence.

Source: https://oeis.org/A094925
Credit: @Solfanbtc

Conjecture (Manfred Scheucher, Jun 03 2015, as stated in the entry):
  a(n) ~ c*phi^n with phi = 1.61803... the golden ratio and
  c = 0.78529667298898361017570049509486675274402985275383398273772345738007479334754...

The sequence. Write the numbers a(1), a(2), ... in a spiral on the hexagonal tiling:
a(1) in a central cell, a(2), ..., a(7) in the six cells around it, a(8), ..., a(19) in the
next ring, and so on, each cell adjacent to the previous one. Then a(1) = 1 and
a(n) = a(n-1) + Sum of the a(i) (i < n-1) in cells adjacent to the cell of a(n-1).
(Examples in the entry: a(4) = a(1) + a(2) + a(3), a(5) = a(1) + a(3) + a(4), ...)

Formalization.
* Hexagonal cells are points of `ℤ × ℤ` in axial coordinates; the six neighbours of `p` are
  `p + d` for `d` in `dirs`.
* The spiral is the walk starting at `(0,0)`, then `(1,0)`, which at each step turns left
  (next direction in `dirs`) when that cell is still free and otherwise goes straight. This is
  the usual hexagonal spiral; the adjacency pattern (all the sequence depends on) is the same
  for every orientation/chirality, by symmetry of the tiling.
* `cells n` lists the cells of a(1), ..., a(n); `terms n` lists a(1), ..., a(n).
* The definitions reproduce all 38 data terms of the entry (checked with `#eval`, and with an
  independent python3 implementation of the same spiral, which with 0 in the centre also
  reproduces the data of the companion A094926). In python3, a(n)/phi^n at n = 1322 is
  0.7852966729889836101756998..., consistent with the conjectured constant.
* The constant is given in the entry by 77 decimals followed by "...". We do not know whether
  it is truncated or rounded, so we require `|c - 0.785...754| < 10^(-77)` (true in both
  readings). `a(n) ~ c * phi^n` with `c ≠ 0` is stated as `a(n) / phi^n → c`.
-/

namespace OMA.S_oeis_a094925

/-- The six neighbour offsets of a hexagonal cell (axial coordinates), counterclockwise. -/
def dirs : List (ℤ × ℤ) := [(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)]

/-- Cells `p` and `q` of the hexagonal tiling are adjacent. -/
def adj (p q : ℤ × ℤ) : Bool := dirs.contains (q.1 - p.1, q.2 - p.2)

/-- One step of the spiral walk: from the visited cells (most recent first) and the current
heading `h`, turn left if the cell there is free, otherwise go straight. -/
def step (s : List (ℤ × ℤ) × ℕ) : List (ℤ × ℤ) × ℕ :=
  let p := s.1.headD (0, 0)
  let l := (s.2 + 1) % 6
  let dl := dirs.getD l (0, 0)
  let cl := (p.1 + dl.1, p.2 + dl.2)
  if s.1.contains cl then
    let ds := dirs.getD s.2 (0, 0)
    ((p.1 + ds.1, p.2 + ds.2) :: s.1, s.2)
  else (cl :: s.1, l)

/-- The cells of a(1), ..., a(n), in order. -/
def cells (n : ℕ) : List (ℤ × ℤ) :=
  ((step^[n - 2] ([(1, 0), (0, 0)], 1)).1.reverse).take n

/-- `terms n = [a(1), ..., a(n)]`. -/
def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | (n + 2) =>
    let L := terms (n + 1)
    let C := cells (n + 1)
    let c := C.getD n (0, 0)
    let s := ((List.range n).filter (fun i => adj (C.getD i (0, 0)) c)).map
      (fun i => L.getD i 0)
    L ++ [L.getD n 0 + s.sum]

/-- A094925(n), offset 1. -/
def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main :
    ∃ c : ℝ, Filter.Tendsto (fun n : ℕ => (a n : ℝ) / Real.goldenRatio ^ n)
        Filter.atTop (nhds c) ∧
      |c - 0.78529667298898361017570049509486675274402985275383398273772345738007479334754| <
        (10 : ℝ) ^ (-77 : ℤ) := by
  sorry

end OMA.S_oeis_a094925
