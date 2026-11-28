import Mathlib

/-!
# A143527: Array D of denominators of Best Remaining Lower Approximates of x=sqrt(2), by antidiagonals.

Source: https://oeis.org/A143527
Credit: @Solfanbtc

Kimberling's construction (OEIS A143527, %F), for `x = √2`: the rows of the array `D` are built
successively. Given the set `U` of denominators used in the earlier rows, row `n` consists, in
increasing order, of the positive integers `q ∉ U` for which some `p` gives a lower approximate
`p/q` (`0 < x - p/q`) strictly better than every lower approximate `c/d` (`c, d > 0`, `c/d < x`)
with `0 < d < q`, `d ∉ U` ("the best remaining lower approximate when all better lower
approximates are unavailable"). `N(n,k) = p = ⌊q x⌋` (the source's fact (4)), `R = N/D`.
Notes on the reading:
* the comparison is with lower approximates `c/d < x` only: for `c/d > x` the inequality
  `x - p/q < x - c/d` cannot hold, so the literal "every positive rational" reading would be
  empty;
* "remaining" excludes only the denominators of the earlier rows: earlier entries of the
  current row are still compared against (otherwise `q = 2` would join row 1, contrary to the data).
With these conventions a python3 computation reproduces all 65 listed terms (by antidiagonals:
`D(1,1); D(1,2), D(2,1); ...`), e.g. row 1 = 1, 3, 5, 17, 29, 99, ... and row 2 = 2, 4, 6, 8, 10, 22, ...

Conjectures (C. Kimberling, OEIS A143527): for consecutive terms `p/q`, `s/t` of row `n ≥ 1` of `R`,
(5) `(s - p)/(t - q)` is an upper principal convergent to `x` (a continued-fraction convergent of
    `√2` that exceeds `√2`), and
(6) `q s - p t = n`.
Both checked with python3 on rows 1..12 for denominators up to 20000.
-/

namespace OMA.S_oeis_a143527

/-- `q` is a best remaining lower approximate denominator of `√2` when the denominators in `U`
are unavailable. -/
def IsBestRemaining (U : Set ℕ) (q : ℕ) : Prop :=
  0 < q ∧ q ∉ U ∧ ∃ p : ℤ, 0 < Real.sqrt 2 - (p : ℝ) / q ∧
    ∀ c d : ℕ, 0 < c → 0 < d → d < q → d ∉ U → (c : ℝ) / d < Real.sqrt 2 →
      Real.sqrt 2 - (p : ℝ) / q < Real.sqrt 2 - (c : ℝ) / d

/-- `used n`: the denominators in rows `1, ..., n`. -/
def used : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 => used n ∪ {q | IsBestRemaining (used n) q}

/-- Row `n` (`n ≥ 1`) of the array `D`, as a set of denominators. -/
def row (n : ℕ) : Set ℕ := {q | IsBestRemaining (used (n - 1)) q}

/-- The numerator `N = ⌊q √2⌋` belonging to the denominator `q`. -/
noncomputable def num (q : ℕ) : ℤ := ⌊(q : ℝ) * Real.sqrt 2⌋

/-- Kimberling's conjectures (5) and (6) for consecutive terms of each row. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ q t : ℕ, q ∈ row n → t ∈ row n → q < t →
    (∀ u ∈ row n, ¬ (q < u ∧ u < t)) →
    (∃ m : ℕ, (GenContFract.of (Real.sqrt 2)).convs m = ((num t - num q : ℤ) : ℝ) / ((t : ℝ) - q) ∧
      Real.sqrt 2 < ((num t - num q : ℤ) : ℝ) / ((t : ℝ) - q)) ∧
    (q : ℤ) * num t - num q * t = n := by
  sorry

end OMA.S_oeis_a143527
