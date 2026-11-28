import Mathlib

/-!
# A017101: a colony of n blocks of Langton's ants has period 4(8n + 3)

Source: https://oeis.org/A017101
Credit: @Solfanbtc

A017101: `a(n) = 8n + 3`.

Conjecture (in the entry, see the MathOverflow link there): "2*a(n) is the half-period of
oscillation of a Langton's ant colony that is n basic blocks in length. To construct such blocks
use a pair of ants facing north at (x,y) and (x+1,y+2) (using Golly's coordinate system). Each
successive block is placed 1 cell away from the previous one, i.e., the x coordinate shifts by 3,
so we have (x+3k,y) and (x+3k+1,y+2). Also, because of the symmetry of the oscillation pattern,
4*a(n) is the length of the whole period."

What is stated. "Half-period" is not given a precise meaning (at time `2a(n)` the grid is in
general not blank, e.g. 16 black cells for `n = 2`), so `main` states the precise claim: for
`n ≥ 1`, starting from an all-white grid with the `2n` ants above, the least `t ≥ 1` after which
the grid is all white again and every ant is back at its initial cell and heading is
`4 a(n) = 32n + 12`.

Model. Cells of `ℤ × ℤ` with Golly's convention that `y` grows downwards (north is `(0, -1)`);
headings `0, 1, 2, 3` = N, E, S, W. Langton's rule: an ant on a white cell turns right (clockwise),
on a black cell turns left; it flips the colour of its cell and moves one cell forward. The entry
does not say how several ants are updated within one time step; we move the ants one after
another in a fixed order (block `k`'s lower ant, then its upper ant, for `k = 0, …, n-1`) within
each step. Checked with python3: with this rule, and also with simultaneous updates (all ants read
their cells, then all occupied cells flip), the period is `4(8n + 3)` for `1 ≤ n ≤ 8` (resp.
`n ≤ 6`).
-/

namespace OMA.S_oeis_a017101

/-- A017101: `a(n) = 8n + 3`. -/
def a (n : ℕ) : ℕ := 8 * n + 3

/-- The unit step for a heading: N, E, S, W in Golly's coordinates. -/
def dirVec (d : ZMod 4) : ℤ × ℤ :=
  if d = 0 then (0, -1) else if d = 1 then (1, 0) else if d = 2 then (0, 1) else (-1, 0)

/-- A configuration: the set of black cells and the list of ants (cell, heading). -/
abbrev Config := Finset (ℤ × ℤ) × List ((ℤ × ℤ) × ZMod 4)

/-- Move one ant on the grid `black`; returns the new grid and the moved ant. -/
def moveAnt (black : Finset (ℤ × ℤ)) (ant : (ℤ × ℤ) × ZMod 4) :
    Finset (ℤ × ℤ) × ((ℤ × ℤ) × ZMod 4) :=
  let c := ant.1
  let d := if c ∈ black then ant.2 - 1 else ant.2 + 1
  let black' := if c ∈ black then black.erase c else insert c black
  (black', (c + dirVec d, d))

/-- One time step: the ants move one after another, in list order. -/
def step (s : Config) : Config :=
  let r := s.2.foldl (fun (acc : Finset (ℤ × ℤ) × List ((ℤ × ℤ) × ZMod 4)) ant =>
    let m := moveAnt acc.1 ant
    (m.1, acc.2 ++ [m.2])) (s.1, [])
  r

/-- The colony of `n` blocks: ants facing north at `(3k, 0)` and `(3k + 1, 2)`, all cells white. -/
def initial (n : ℕ) : Config :=
  (∅, (List.range n).flatMap fun k => [(((3 * k : ℤ), 0), 0), (((3 * k + 1 : ℤ), 2), 0)])

/-- The conjecture: the colony of `n ≥ 1` blocks has period exactly `4 a(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    IsLeast {t : ℕ | 1 ≤ t ∧ step^[t] (initial n) = initial n} (4 * a n) := by
  sorry

end OMA.S_oeis_a017101
