import Mathlib

/-!
# A051233: Number of unit squares at least 50% covered by a circle inscribed in an integer square of size n X n.

Source: https://oeis.org/A051233
Credit: @Solfanbtc

In the square `[0, n]²`, divided into the `n²` unit squares `[i, i+1] × [j, j+1]`, consider the
inscribed disc `D` (center `(n/2, n/2)`, radius `n/2`).
* A051233(n): the number of unit squares with at least half of their area in `D`
  (`1, 4, 9, 12, 21, 32, ...`);
* A124623(n): the number of unit squares whose center lies (strictly) within the circle, i.e.
  `(i + 1/2 - n/2)² + (j + 1/2 - n/2)² < n²/4` (as in the entry's Mathematica program).

Conjecture (Sean A. Irvine, Sep 03 2021, in the entry): `A051233(n) ≤ A124623(n)`, with equality in
most cases. Stated: the inequality for every `n ≥ 1`. ("With equality in most cases" is not made
precise in the entry and is not part of the statement.)

A python3 check (numerical areas): the area definition reproduces the first 30 data terms, and
for all `n ≤ 51` (the data) `A051233(n) = A124623(n)`.

Conventions: areas are Lebesgue measure on `ℝ × ℝ` (`MeasureTheory.volume`); the disc is closed
(its boundary has measure zero, so this does not affect the areas).
-/

namespace OMA.S_oeis_a051233

open MeasureTheory

/-- The inscribed (closed) disc of the `n × n` square `[0, n]²`. -/
def disc (n : ℕ) : Set (ℝ × ℝ) :=
  {p | (p.1 - n / 2) ^ 2 + (p.2 - n / 2) ^ 2 ≤ ((n : ℝ) / 2) ^ 2}

/-- The unit square `[i, i+1] × [j, j+1]`. -/
def cell (i j : ℕ) : Set (ℝ × ℝ) := Set.Icc (i : ℝ) (i + 1) ×ˢ Set.Icc (j : ℝ) (j + 1)

/-- A051233(n): unit squares at least half covered by the inscribed disc. -/
noncomputable def covered (n : ℕ) : ℕ :=
  {c : Fin n × Fin n | (1 : ℝ) / 2 ≤ (volume (cell c.1 c.2 ∩ disc n)).toReal}.ncard

/-- A124623(n): unit squares whose center lies within the inscribed circle. -/
noncomputable def centered (n : ℕ) : ℕ :=
  {c : Fin n × Fin n |
    ((c.1 : ℝ) + 1 / 2 - n / 2) ^ 2 + ((c.2 : ℝ) + 1 / 2 - n / 2) ^ 2 < ((n : ℝ) / 2) ^ 2}.ncard

/-- Irvine's conjecture: `A051233(n) ≤ A124623(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → covered n ≤ centered n := by
  sorry

end OMA.S_oeis_a051233
