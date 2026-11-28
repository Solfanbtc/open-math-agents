import Mathlib

/-!
# A116473: Number of partitions with exactly n subpartitions.

Source: https://oeis.org/A116473
Credit: @Solfanbtc

Conjecture (Franklin T. Adams-Watters, OEIS A116473, %C line): `lim_{n → ∞} a(n) = ∞`.

Definitions (A115728, A115729).
* A subpartition of a partition `λ = (λ₁ ≥ λ₂ ≥ ... ≥ λ_k)` is a partition
  `μ = (μ₁ ≥ ... ≥ μ_k ≥ 0)` with `μ_i ≤ λ_i` for all `i` (trailing zeros = fewer parts); the empty
  partition and `λ` itself count, e.g. `[2,1]` has the 5 subpartitions `[], [1], [2], [1,1], [2,1]`.
* `a(n)` is the number of partitions `λ` (of any integer `m ≥ 0`, the empty partition included)
  with exactly `n` subpartitions; `a(1) = 1` counts only the empty partition.

Formalization.
* `subCount l` counts the weakly decreasing sequences `μ` with `0 ≤ μ_i ≤ l_i`, for `l` the parts
  of `λ` in decreasing order: `go (x :: xs) c` lets the next part of `μ` be any `j ≤ min x c`
  (`c` = previous part of `μ`).
* A partition of `m` has at least `m + 1` subpartitions (`[]`, `[1]`, `[2]`, ..., `[λ₁, ...]`
  grow one cell at a time), so the partitions with exactly `n` subpartitions are partitions of
  some `m < n`; `a n` sums over those `m`, which makes it a finite count.

Checked with python3 (pruned enumeration): these definitions reproduce all listed %S/%T/%U
terms (`n ≤ 81`); `#eval` of the Lean `a` gives `1, 1, 2, 2, 3, 3, 4, 2` for `n = 1..8`.
-/

namespace OMA.S_oeis_a116473

open Filter

/-- Weakly decreasing `μ` with `μ_i ≤ l_i` and every part `≤ c`. -/
def go : List ℕ → ℕ → ℕ
  | [], _ => 1
  | x :: xs, c => ∑ j ∈ Finset.range (min x c + 1), go xs j

/-- The number of subpartitions of the partition with parts `l` (in decreasing order). -/
def subCount (l : List ℕ) : ℕ := go l (l.headD 0)

/-- The number of subpartitions of a partition `λ` of `m`. -/
def subCountP {m : ℕ} (p : Nat.Partition m) : ℕ := subCount (p.parts.sort (· ≥ ·))

/-- A116473: the number of partitions (of any `m`, necessarily `m < n`) with exactly `n`
subpartitions. -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n, (Finset.univ.filter (fun p : Nat.Partition m => subCountP p = n)).card

/-- `a(n) → ∞`. -/
theorem main : Tendsto a atTop atTop := by
  sorry

end OMA.S_oeis_a116473
