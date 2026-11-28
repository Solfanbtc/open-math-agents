import Mathlib

/-!
# A247556: an exact differential base (B_2 sequence); gaps and growth conjectures

Source: https://oeis.org/A247556
Credit: @Solfanbtc

A247556 (T. Ordowski; offset 0): start with `a(0) = 0`. Given `a(0), …, a(n-1)`, let `d` be the
smallest positive integer that is not a difference `a(j) - a(i)` (`i < j`). If appending
`a(n-1) + d` causes no difference to be repeated, then `a(n) = a(n-1) + d`. Otherwise, let `r`
be the smallest positive integer such that appending both `a(n) = a(n-1) + r` and
`a(n+1) = a(n) + d` causes no difference to be repeated. (This is the reading of the entry's
second comment: "r is the smallest integer that allows this assignment of a(n) and a(n+1)
without causing any difference to be repeated"; with python3 it reproduces all 50 listed terms.)
Every positive integer is then a difference of two terms in exactly one way.

The entry has two conjectures, and `main` states both:
* (%C) `lim inf_{n->oo} (a(n+1) - a(n))/n = 1/2`;
* (%F) `a(n) ~ log(log(n)) * A025582(n+1)`, where `A025582(m) + 1 = A005282(m)` is the
  Mian-Chowla sequence. A025582 (offset 1) is `0, 1, 3, 7, 12, 20, 30, 44, 65, 80, 96, 122, …`:
  `b(1) = 0` and `b(m+1)` is the least integer `> b(m)` keeping all differences distinct. Below,
  `mianChowla n = A025582(n+1)`.

Lean details. Both sequences are built as lists by appending terms. Searches are bounded:
`d ≤ #differences + 1` (pigeonhole), and if `M` is the last term then `r = M + 2` always works,
and for Mian-Chowla `x = 2M + 1` always works (all new differences exceed every old one), so the
`find?` searches always succeed and the defaults `0` are never used. Each step appends at least
one term, so `build n` has at least `n + 1` terms and `a n` is its entry `n` (the lists only grow
by appending). `Filter.liminf` is the real lim inf; the sequence is nonnegative, and the value
`1/2` cannot arise as a junk value. Numerically (python3, `n ≤ 500`), `min_{n/2 ≤ k < n}
(a(k+1) - a(k))/k` decreases slowly (1.30 at `n = 100`, 1.02 at `n = 500`) and
`a(n)/(log log n · A025582(n+1))` stays near 0.9.
-/

namespace OMA.S_oeis_a247556

/-- All differences `l[j] - l[i]` with `i < j`. -/
def diffs (l : List ℕ) : List ℕ :=
  (List.range l.length).flatMap fun j =>
    (List.range j).map fun i => l.getD j 0 - l.getD i 0

/-- All differences of `l` are distinct (a B_2 / Sidon-type condition on differences). -/
def DistinctDiffs (l : List ℕ) : Prop := (diffs l).Nodup

instance (l : List ℕ) : Decidable (DistinctDiffs l) := by
  unfold DistinctDiffs; infer_instance

/-- One construction step of A247556. -/
def extend (l : List ℕ) : List ℕ :=
  let M := l.getLastD 0
  let d := ((List.range' 1 ((diffs l).length + 1)).find? (fun x => decide (x ∉ diffs l))).getD 0
  if DistinctDiffs (l ++ [M + d]) then l ++ [M + d]
  else
    let r := ((List.range' 1 (M + 2)).find?
      (fun x => decide (DistinctDiffs (l ++ [M + x, M + x + d])))).getD 0
    l ++ [M + r, M + r + d]

/-- The list obtained after `k` construction steps, starting from `[0]`. -/
def build : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => extend (build k)

/-- A247556: `a(n)`. -/
def a (n : ℕ) : ℕ := (build n).getD n 0

/-- One step of the Mian-Chowla greedy construction (A025582). -/
def extendMC (l : List ℕ) : List ℕ :=
  let M := l.getLastD 0
  l ++ [((List.range' (M + 1) (M + 1)).find? (fun x => decide (DistinctDiffs (l ++ [x])))).getD 0]

/-- `mianChowla n = A025582(n+1)`: `0, 1, 3, 7, 12, 20, 30, 44, 65, 80, 96, 122, …`. -/
def mianChowla (n : ℕ) : ℕ := ((extendMC^[n]) [0]).getD n 0

open Filter Topology in
/-- Both conjectures of A247556: `liminf (a(n+1) - a(n))/n = 1/2`, and
`a(n) ~ log(log(n)) * A025582(n+1)`. -/
theorem main :
    liminf (fun n : ℕ => ((a (n + 1) : ℝ) - a n) / n) atTop = 1 / 2 ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / (Real.log (Real.log n) * mianChowla n)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a247556
