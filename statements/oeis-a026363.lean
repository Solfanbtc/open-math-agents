import Mathlib

/-!
# A026363: -1 < n (1 + √3)/2 - a(n) < 2

Source: https://oeis.org/A026363
Credit: @Solfanbtc

A026362 (offset 1): `s(n) = s(m)` if `s(m)` has already occurred exactly once and
`n = s(m) + 2m - 1`, else `s(n)` is the least positive integer that has not yet occurred.
Data 1, 1, 2, 3, 4, 5, 2, 6, 7, 3, 8, 9, 4, …
A026363 (offset 1): `a(n)` is the least `k` such that `s(k) = n`. Data 1, 3, 4, 5, 6, 8, 9, 11, …

Conjecture (C. Kimberling, Apr 29 2017): `-1 < n*r - a(n) < 2` for `n ≥ 1`, where
`r = (1 + sqrt(3))/2`.

Definition of A026362 in Lean: the terms are built one at a time; for the `n`-th term, with the
earlier terms `s(1), …, s(n-1)` known, we look for an `m < n` with `n = s(m) + 2m - 1` such that
`s(m)` occurs exactly once among the earlier terms, taking the least such `m` (python3: for
`n ≤ 2·10^4` the candidates never disagree), and otherwise take the least positive integer not
yet used. Checked with python3: this reproduces the data of both sequences, and the inequality
holds for `1 ≤ n ≤ 14641` (`n r - a(n)` ranges over about `[-0.940, 1.322]` there).
-/

namespace OMA.S_oeis_a026363

/-- Append the next term of A026362 to the list `l = [s(1), …, s(n-1)]` (so `n = l.length + 1`). -/
def extend (l : List ℕ) : List ℕ :=
  let n := l.length + 1
  let cand := (List.range' 1 l.length).find? fun m =>
    l.getD (m - 1) 0 + 2 * m - 1 == n && l.count (l.getD (m - 1) 0) == 1
  match cand with
  | some m => l ++ [l.getD (m - 1) 0]
  | none => l ++ [((List.range' 1 (l.length + 1)).find? fun v => !(l.contains v)).getD 0]

/-- A026362: `s(n)` (for `n ≥ 1`). -/
def s (n : ℕ) : ℕ := ((extend)^[n] []).getD (n - 1) 0

/-- A026363: the least `k ≥ 1` with `s(k) = n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ s k = n}

/-- Kimberling's conjecture: `-1 < n r - a(n) < 2` with `r = (1 + √3)/2`, for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * ((1 + Real.sqrt 3) / 2) - a n ∧ (n : ℝ) * ((1 + Real.sqrt 3) / 2) - a n < 2 := by
  sorry

end OMA.S_oeis_a026363
