import Mathlib

/-!
# A026367: a(n) = least k such that s(k) = n, where s = A026366.

Source: https://oeis.org/A026367
Credit: @Solfanbtc

Conjecture (Clark Kimberling, OEIS A026367, comment, Apr 29 2017):
-1 < n*r - a(n) < 2 for n >= 1, where r = (1 + sqrt(3))/2.

Conventions:
* s = A026366 (offset 1) is defined by its name: s(n) = s(m) if s(m) has already occurred
  exactly once (among s(1), ..., s(n-1)) and n = s(m) + 2m (for some m < n), else s(n) is the
  least positive integer that has not yet occurred. In `next` below, when several m would
  qualify the least one is used; in Python no n ≤ 3000 has more than one qualifying m, so this
  choice does not matter there. This gives 1, 2, 1, 3, 4, 2, 5, 6, 7, 8, 3, ... (the data of
  A026366).
* a(n) is the least k ≥ 1 with s(k) = n. Checked in Python: all 63 listed terms of A026367,
  and the conjectured inequality for 1 ≤ n < 400.
-/

namespace OMA.S_oeis_a026367

/-- Given the list `[s(1), ..., s(n-1)]`, the value `s(n)`. -/
def next (l : List ℕ) : ℕ :=
  match (List.range l.length).find? (fun i =>
      l.getD i 0 + 2 * (i + 1) = l.length + 1 ∧ l.count (l.getD i 0) = 1) with
  | some i => l.getD i 0
  | none => ((List.range (l.length + 2)).find? (fun k => 0 < k ∧ k ∉ l)).getD 0

/-- The list `[s(1), ..., s(n)]`. -/
def prefixList : ℕ → List ℕ
  | 0 => []
  | n + 1 => prefixList n ++ [next (prefixList n)]

/-- A026366 (offset 1): `s n` for `n ≥ 1`. -/
def s (n : ℕ) : ℕ := (prefixList n).getLastD 0

/-- A026367: the least `k ≥ 1` with `s(k) = n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ s k = n}

/-- Kimberling's conjecture: `-1 < n r - a(n) < 2` with `r = (1 + √3)/2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * ((1 + Real.sqrt 3) / 2) - a n ∧
      (n : ℝ) * ((1 + Real.sqrt 3) / 2) - a n < 2 := by
  sorry

end OMA.S_oeis_a026367
