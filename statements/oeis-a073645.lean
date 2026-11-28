import Mathlib

/-!
# A073645: a(1)=2 and, for all n>=1, a(n) is the length of the n-th run of increasing consecutive integers with each run after the first starting with 1.

Source: https://oeis.org/A073645
Credit: @Solfanbtc

Conjecture (OEIS entry, %F, John W. Layman 2002): let `P(k) = 1 + k/3 + k^2/2 + k^3/6`. Then
`a(n) = 3` if `n = P(k)` for some `k`, `a(n) = 2` if `P(k-1) < n < P(k)` for some `k` and
`P(k) - n = m(m+1)/2` for some `m`, else `a(n) = 1`.
Benoit Cloitre (2009, %C) remarks that without its initial 2 the sequence is the fixed point of
the morphism `3 → 123, 2 → 12, 1 → 1`, "thus the given formulas are exact", i.e. the conjecture
is claimed to be proved.

Conventions and the minimal fix:
* The sequence is built as in the entry's PARI program: start from `[2, 3]` and, for
  `n = 2, 3, …`, append the run `1, 2, …, a(n)`. `build j` is the list after `j` such steps; it
  has more than `j + 1` entries, so `a(n)` (offset 1) is entry `n - 1` of `build n`. This
  reproduces all 105 listed terms (%S, %T, %U), checked in Python.
* The formula fails at `n = 1`: `1 = P(0)` would give `a(1) = 3`, while `a(1) = 2` by definition
  (the morphism description also excludes the initial 2). We therefore state it for `n ≥ 2`; there
  `k` ranges over the naturals (`P(0) = 1 < n`). Checked in Python for `2 ≤ n ≤ 50000`: the formula
  then holds, and `n = 1` is the only exception.
* `P(k)` is evaluated in `ℚ` (it is always an integer, `1 + C(k+2, 3)`); in the middle case
  `k ≥ 1`, so that `k - 1` is a natural number, and `m` ranges over the naturals.
-/

namespace OMA.S_oeis_a073645

/-- After `j` steps: `[2, 3]` followed by the runs `1, …, a(n)` for `n = 2, …, j + 1`. -/
def build : ℕ → List ℕ
  | 0 => [2, 3]
  | j + 1 =>
    let L := build j
    L ++ (List.range (L.getD (j + 1) 0)).map (· + 1)

/-- `a(n)` (offset 1). -/
def a (n : ℕ) : ℕ := (build n).getD (n - 1) 0

/-- `P(k) = 1 + k/3 + k^2/2 + k^3/6`. -/
def P (k : ℕ) : ℚ := 1 + k / 3 + k ^ 2 / 2 + k ^ 3 / 6

open Classical in
/-- Layman's formula for A073645, for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n = if ∃ k : ℕ, (n : ℚ) = P k then 3
      else if ∃ k : ℕ, 1 ≤ k ∧ P (k - 1) < n ∧ (n : ℚ) < P k ∧
          ∃ m : ℕ, P k - n = m * (m + 1) / 2 then 2
      else 1 := by
  sorry

end OMA.S_oeis_a073645
