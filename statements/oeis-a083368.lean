import Mathlib

/-!
# A083368: a(n) is the position of the highest one in A003754(n).

Source: https://oeis.org/A083368 (with A003754, A245563, A385817)
Credit: @Solfanbtc

**The sequence.** A003754 lists the numbers with no two adjacent 0's in their binary
expansion: `0, 1, 2, 3, 5, 6, 7, 10, …` (offset 1). The binary expansion of `A003754(n+1)` is the
lazy Fibonacci ("Fibbinary, no adjacent zeros") representation of `n`, and by the entry's
previous name `a(n)` (`n ≥ 1`) is the highest bit position (counted from 1) that changes going
from the representation of `n - 1` to that of `n`, i.e. the position of the highest one of
`A003754(n) xor A003754(n+1)`. (The current short name, read literally on `A003754(n)`, does not
reproduce the data, e.g. it would give `a(3) = 2`; the definition used here reproduces the
listed data `a(1..102)`, checked numerically.) We write `fibb k` for `A003754(k+1)`, so
`fibb 0 = 0`, and `a(n) = Nat.log 2 (fibb n xor fibb (n-1)) + 1`.

**The conjecture** (Gus Wiseman, Jul 24 2025). A245563 lists, for each `m ≥ 0`, the lengths of the
maximal runs of 1's in the binary expansion of `m`, starting with the low-order bits. Removing the
empty row (`m = 0`) and every row equal to an earlier row gives the rows of A385817 (rows `1, 2, …`;
its row `0` is the empty row). The conjecture: the first term of the `k`-th remaining row is
`a(k)`, for every `k ≥ 1`.

Formally, `m` is a *first appearance* if no `j < m` has the same run-length list; the first
appearances in increasing order are `0, 1, 3, 5, 7, …` (`Nat.nth` index `0, 1, 2, …`), the one of
index `0` being `m = 0` with the empty row, so the `k`-th row of A385817 is the run-length list of
the first appearance of index `k`. Checked numerically for `1 ≤ k < 46367`.
-/

namespace OMA.S_oeis_a083368

/-- No two adjacent 0's in the binary expansion of `m` (A003754). -/
def NoAdjZeros (m : ℕ) : Prop := ¬ [0, 0] <:+: Nat.digits 2 m

instance : DecidablePred NoAdjZeros := fun m => by unfold NoAdjZeros; infer_instance

/-- `fibb k = A003754(k + 1)`: the `k`-th (from `0`) number with no adjacent zeros in binary. -/
noncomputable def fibb (k : ℕ) : ℕ := Nat.nth NoAdjZeros k

/-- A083368(n), for `n ≥ 1`: the position (from 1) of the highest bit that changes from
`fibb (n-1)` to `fibb n`. -/
noncomputable def a083368 (n : ℕ) : ℕ := Nat.log 2 (fibb n ^^^ fibb (n - 1)) + 1

/-- Row `m` of A245563: lengths of the maximal runs of 1's in the binary expansion of `m`,
low-order bits first (`[]` for `m = 0`). -/
def runLengths (m : ℕ) : List ℕ :=
  (((Nat.digits 2 m).splitOn 0).filter (fun l => l ≠ [])).map List.length

/-- `m` is the first index of its row in A245563. -/
def IsFirstAppearance (m : ℕ) : Prop := ∀ j < m, runLengths j ≠ runLengths m

/-- Conjecture (Gus Wiseman, OEIS A083368): the first term of row `k` of A385817 (A245563 with
empty and duplicate rows removed) is A083368(k), for every `k ≥ 1`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (runLengths (Nat.nth IsFirstAppearance k)).head? = some (a083368 k) := by
  sorry

end OMA.S_oeis_a083368
