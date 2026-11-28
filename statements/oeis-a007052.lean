import Mathlib

/-!
# A007052: Number of order-consecutive partitions of n

Source: https://oeis.org/A007052
Credit: @Solfanbtc

A007052 (offset 0): `1, 3, 10, 34, 116, 396, 1352, 4616, …`, with `a(n) = 4 a(n-1) - 2 a(n-2)`,
`a(0) = 1`, `a(1) = 3` (OEIS formula; equivalently g.f. `(1-x)/(1-4x+2x^2)`). Below, `A007052`
is defined by this recurrence; it reproduces all 29 data terms.

Conjecture (Gus Wiseman, Mar 05 2020, OEIS comment): `a(n)` is also the number of ordered set
partitions of `{1, …, n+1}` where no element of any block is greater than any element of a
non-adjacent consecutive (i.e. later) block: for blocks `B_1, …, B_k` (in order), whenever
`j ≥ i + 2`, every element of `B_i` is less than every element of `B_j`. (Example in the source:
for `n = 2` these are the 10 listed partitions; e.g. `{{2},{1},{3}}` is counted, `{{2},{3},{1}}`
is not.)

Encoding: an ordered set partition of `Fin (n+1)` into `k` (nonempty) blocks is the same as a
surjection `f : Fin (n+1) → Fin k` (block of `x` is `f x`). The condition reads: if
`f x + 2 ≤ f y` then `x < y` (`x ≠ y` as they lie in different blocks). The number of ordered
set partitions is the sum over `k ≤ n + 1` (more blocks than elements is impossible) of the
number of such surjections. A brute-force count with these definitions gives
`1, 3, 10, 34, 116, 396, 1352` for `n = 0..6`, matching the sequence.
-/

namespace OMA.S_oeis_a007052

/-- A007052 by its recurrence `a(n) = 4 a(n-1) - 2 a(n-2)`, `a(0) = 1`, `a(1) = 3`. -/
def A007052 : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | n + 2 => 4 * A007052 (n + 1) - 2 * A007052 n

/-- An ordered set partition of `Fin m` into `k` blocks, given as the surjection `f` sending each
element to the index of its block, in which every element of block `i` is less than every
element of block `j` whenever `j ≥ i + 2`. -/
def Good (m k : ℕ) (f : Fin m → Fin k) : Prop :=
  Function.Surjective f ∧ ∀ x y : Fin m, (f x : ℕ) + 2 ≤ f y → x < y

instance (m k : ℕ) : DecidablePred (Good m k) := fun f => by
  unfold Good; infer_instance

/-- Number of ordered set partitions of `{1, …, m}` with the non-adjacent-block condition. -/
def count (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), (Finset.univ.filter (Good m k)).card

/-- Wiseman's conjecture: for every `n`, the number of such ordered set partitions of
`{1, …, n+1}` equals A007052(n). -/
theorem main : ∀ n : ℕ, (count (n + 1) : ℤ) = A007052 n := by
  sorry

end OMA.S_oeis_a007052
