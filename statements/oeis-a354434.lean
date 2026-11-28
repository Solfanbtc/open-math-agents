import Mathlib

/-!
# A354434: a(1) = 1; for n > 1, a(n) is the smallest unused square spiral number such that a(n) shares a factor with all existing numbers in its Moore neighborhood.

Source: https://oeis.org/A354434
Credit: @Solfanbtc

The numbers are placed on the square spiral: `a(1) = 1` at the origin, then the spiral goes
right, up, left, down with side lengths `1, 1, 2, 2, 3, 3, ...` (as in the entry's picture:
`2` right of `1`, then `4, 6, 3` above, `9` left of `1`, ...). For `n > 1`, `a(n)` is the smallest
number not used before that shares a factor (`gcd > 1`) with every number already placed in the
8 cells around its cell. The `1` at the origin is ignored in this test (otherwise no `a(n)` could
be placed next to it; the data has `a(2) = 2` next to `1`). Data: `1, 2, 4, 6, 3, 9, 12, 18, 8, ...`.

Conjecture (the entry): the sequence is a permutation of the positive integers (e.g.
`a(1807) = 13`, `a(35156) = 179`; after a million terms 397, 419, ... are still missing).

Conventions:
* `spiralStep` walks the spiral; its state is (cell, segment index `k`, steps done in segment
  `k`), segment `k` having length `k / 2 + 1` and direction `k % 4` (right, up, left, down).
* `placed n` is the list of (cell, value) for `a(1), ..., a(n+1)`, newest first.
* The smallest admissible value is found by `firstFrom`, testing `2, 3, ...` in order with a fuel
  bound `(M + 1) * P + 1`, where `M` is the largest used value and `P` the product of the
  neighbors `≠ 1`: the value `(M + 1) * P` is unused and shares a factor with every such
  neighbor, so the search always succeeds within the bound.
* A python3 mirror reproduces all 75 data terms, and the Lean kernel (`decide`) confirms
  `a 1, ..., a 12 = 1, 2, 4, 6, 3, 9, 12, 18, 8, 10, 14, 16`.
-/

namespace OMA.S_oeis_a354434

/-- Direction of segment `k` of the spiral: right, up, left, down. -/
def dir (k : ℕ) : ℤ × ℤ :=
  match k % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

/-- One step along the spiral: (cell, segment index, steps done in the current segment). -/
def spiralStep (s : (ℤ × ℤ) × ℕ × ℕ) : (ℤ × ℤ) × ℕ × ℕ :=
  let c := s.1
  let k := s.2.1
  let d := s.2.2
  let c' := (c.1 + (dir k).1, c.2 + (dir k).2)
  if d + 1 = k / 2 + 1 then (c', k + 1, 0) else (c', k, d + 1)

/-- The cell of the `n`-th spiral number (0-indexed: `cell 0` is the origin, holding `a(1)`). -/
def cell (n : ℕ) : ℤ × ℤ := (spiralStep^[n] ((0, 0), 0, 0)).1

/-- The first `v ≥ start` (testing at most `fuel + 1` values) with `p v`. -/
def firstFrom (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, v => v
  | fuel + 1, v => if p v then v else firstFrom p fuel (v + 1)

/-- Values already placed in the 8 cells around `c`. -/
def neighbors (L : List ((ℤ × ℤ) × ℕ)) (c : ℤ × ℤ) : List ℕ :=
  (L.filter fun e => e.1 ≠ c && |e.1.1 - c.1| ≤ 1 && |e.1.2 - c.2| ≤ 1).map (·.2)

/-- The next value placed at cell `c`, given the placed entries `L`. -/
def nextValue (L : List ((ℤ × ℤ) × ℕ)) (c : ℤ × ℤ) : ℕ :=
  let nb := (neighbors L c).filter (· ≠ 1)
  let M := (L.map (·.2)).foldr max 0
  firstFrom (fun v => !((L.map (·.2)).contains v) && nb.all (fun m => 1 < Nat.gcd v m))
    ((M + 1) * nb.prod + 1) 2

/-- `placed n`: (cell, value) of `a(1), ..., a(n + 1)`, newest first. -/
def placed : ℕ → List ((ℤ × ℤ) × ℕ)
  | 0 => [((0, 0), 1)]
  | n + 1 => let L := placed n; (cell (n + 1), nextValue L (cell (n + 1))) :: L

/-- `a n = A354434(n)` for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := ((placed (n - 1)).headD ((0, 0), 0)).2

/-- Conjecture: A354434 is a permutation of the positive integers. -/
theorem main : Set.BijOn a {n | 1 ≤ n} {v | 1 ≤ v} := by
  sorry

end OMA.S_oeis_a354434
