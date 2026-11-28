import Mathlib

/-!
# A116731: distinct (flips, iterations) pairs of bubble sort over all permutations of 1..n

Source: https://oeis.org/A116731
Credit: @Solfanbtc

A116731 (offset 1): the number of permutations of length `n` avoiding the patterns 321, 2143,
3124 (or 132, 2314, 4312, etc.); by the entry's formula (F. T. Adams-Watters)
`a(n) = (n^3 - 3n^2 + 5n)/3`, which we use as the definition. Data 1, 2, 5, 12, 25, 46, 77, …

Conjecture (W. Meeussen, Dec 13 2008): "also counts the distinct pairs (flips, iterations) that a
bubble sort program generates when sorting all permutations of 1..n."

Reading. Bubble sort repeatedly sweeps the list from left to right, swapping each adjacent pair
that is out of order, until a sweep makes no swap. For a permutation, "flips" is the total number
of swaps and "iterations" the number of sweeps that made at least one swap. (Counting the final
swap-free sweep as well would add 1 to every iteration count and not change the number of
distinct pairs.) At most `n` sweeps are needed for a list of length `n`, which we use as fuel.
Checked with python3: the number of distinct pairs is `a(n)` for `1 ≤ n ≤ 9`.
-/

namespace OMA.S_oeis_a116731

/-- A116731 by the entry's formula. -/
def a (n : ℕ) : ℕ := (n ^ 3 + 5 * n - 3 * n ^ 2) / 3

/-- One left-to-right sweep: the resulting list and the number of swaps. -/
def sweep : List ℕ → List ℕ × ℕ
  | x :: y :: rest =>
    if y < x then
      let r := sweep (x :: rest)
      (y :: r.1, r.2 + 1)
    else
      let r := sweep (y :: rest)
      (x :: r.1, r.2)
  | l => (l, 0)
termination_by l => l.length

/-- Bubble sort with `fuel` sweeps: (total swaps, sweeps that swapped). -/
def bubble : ℕ → List ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | fuel + 1, l =>
    let r := sweep l
    if r.2 = 0 then (0, 0)
    else
      let b := bubble fuel r.1
      (b.1 + r.2, b.2 + 1)

/-- The number of distinct (flips, iterations) pairs over all permutations of `1, …, n`. -/
def numPairs (n : ℕ) : ℕ :=
  ((List.range' 1 n).permutations.map (bubble n)).dedup.length

/-- Meeussen's conjecture: `numPairs n = a(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → numPairs n = a n := by
  sorry

end OMA.S_oeis_a116731
