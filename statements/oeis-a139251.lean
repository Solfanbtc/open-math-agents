import Mathlib

/-!
# A139251: toothpicks added between stages 2^(p-1) and 2^p - 1 sum to the perfect number 2^(p-1)(2^p - 1)

Source: https://oeis.org/A139251
Credit: @Solfanbtc

A139250 (offset 0): the toothpick sequence, the number of toothpicks after `n` stages: toothpicks
have length 2; at stage 1 one vertical toothpick is placed with its midpoint at the origin; at
each later stage a new toothpick is placed, perpendicular, at every exposed endpoint, i.e. an
endpoint of a toothpick that touches no other toothpick (neither an end nor a midpoint).
Data 0, 1, 3, 7, 11, 15, 23, 35, 43, … A139251 (offset 0) is its first differences: the number
of toothpicks added at stage `n` (`A139251(0) = 0`); data 0, 1, 2, 4, 4, 4, 8, 12, 8, …

Conjecture (in the entry): "The sum of the toothpicks added to the toothpick structure between
the stage A061652(k) and the stage A000668(k) is equal to the k-th even perfect number, for
k >= 1." A061652(k) = `2^(p-1)` and A000668(k) = `2^p - 1`, where `2^p - 1` is the `k`-th Mersenne
prime, and the `k`-th even perfect number is `2^(p-1)(2^p - 1)` (Euclid-Euler). So `main` states:
for every `p` with `2^p - 1` prime, `Sum_{j = 2^(p-1)}^{2^p - 1} A139251(j) = 2^(p-1)(2^p - 1)`,
the stages being inclusive, as in the entry's examples (`6 = 2 + 4`, `28 = 4 + 4 + 8 + 12`).

Model. A toothpick is (midpoint in `ℤ × ℤ`, vertical?); its ends are the midpoint `± (0, 1)`
(vertical) or `± (1, 0)` (horizontal). An end is exposed if it lies on exactly one toothpick
(counting both ends and midpoints). Checked with python3 by direct simulation: the counts
reproduce the data of A139250, and the identity holds for `2 ≤ p ≤ 8` (also for non-Mersenne
`p`, e.g. `p = 4, 6, 8`).
-/

namespace OMA.S_oeis_a139251

/-- A toothpick: midpoint and orientation (`true` = vertical). -/
abbrev Toothpick := (ℤ × ℤ) × Bool

/-- The two ends of a toothpick. -/
def ends (t : Toothpick) : Finset (ℤ × ℤ) :=
  if t.2 then {(t.1.1, t.1.2 + 1), (t.1.1, t.1.2 - 1)}
  else {(t.1.1 + 1, t.1.2), (t.1.1 - 1, t.1.2)}

/-- The points of a toothpick: its midpoint and its two ends. -/
def pts (t : Toothpick) : Finset (ℤ × ℤ) := insert t.1 (ends t)

/-- The number of toothpicks of `S` containing the point `q`. -/
def occ (S : Finset Toothpick) (q : ℤ × ℤ) : ℕ := (S.filter fun t => q ∈ pts t).card

/-- One stage: add a perpendicular toothpick at every exposed end. -/
def grow (S : Finset Toothpick) : Finset Toothpick :=
  S ∪ (S.biUnion fun t => ((ends t).filter fun e => occ S e = 1).image fun e => (e, !t.2))

/-- The toothpick structure after `n` stages. -/
def structure_ : ℕ → Finset Toothpick
  | 0 => ∅
  | 1 => {((0, 0), true)}
  | n + 2 => grow (structure_ (n + 1))

/-- A139250. -/
def a139250 (n : ℕ) : ℕ := (structure_ n).card

/-- A139251: the number of toothpicks added at stage `n`. -/
def a139251 (n : ℕ) : ℕ := if n = 0 then 0 else a139250 n - a139250 (n - 1)

/-- The conjecture: for each Mersenne prime `2^p - 1`, the toothpicks added at stages
`2^(p-1), …, 2^p - 1` number `2^(p-1)(2^p - 1)`. -/
theorem main : ∀ p : ℕ, (2 ^ p - 1).Prime →
    ∑ j ∈ Finset.Icc (2 ^ (p - 1)) (2 ^ p - 1), a139251 j = 2 ^ (p - 1) * (2 ^ p - 1) := by
  sorry

end OMA.S_oeis_a139251
