import Mathlib

/-!
# A003157: A self-generating sequence (see Comments in A003156 for the definition).

Source: https://oeis.org/A003157
Credit: @Solfanbtc

Definition (N. J. A. Sloane, comment in A003156): the triple `(A003156, A003157, A003158)` is
the rows `a(n), b(n), c(n)` (`n ≥ 1`) of the table with `a(1) = 1, b(1) = 3, c(1) = 2` and
thereafter
* `a(n) = mex {a(i), b(i), c(i) : i < n}` (the least positive integer not yet used),
* `b(n) = a(n) + 2n`,
* `c(n) = b(n) - 1`.
(The case `n = 1` of these rules gives `a(1) = 1, b(1) = 3, c(1) = 2`.)
A003157 is the row `b`: 3, 8, 11, 14, 19, 24, 29, 32, 35, 40, ...

Conjecture (Clark Kimberling, May 07 2017; A003157 is also the sequence of positions of 1 in
A286044, the {011 -> 0}-transform of the Thue-Morse word): `a(n)/n -> 4`.

Sanity check (python): the table reproduces all 58 listed terms of A003157, its `b` row equals the
positions of 1 in A286044 (computed as the Thue-Morse word with each 011 replaced by 0) for the
first 5000 terms, and `b(n)/n` is 3.998, 4.0002, 3.9999 at `n = 1000, 10000, 20000`.
-/

namespace OMA.S_oeis_a003157

/-- The least positive integer not in `l` (it is at most `l.length + 1`). -/
def mex (l : List ℕ) : ℕ :=
  ((List.range (l.length + 2)).find? (fun k => 0 < k ∧ k ∉ l)).getD 0

/-- `used n` lists the values `a(i), b(i), c(i)` for `1 ≤ i ≤ n`. -/
def used : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let x := mex (used n)
    x :: (x + 2 * (n + 1)) :: (x + 2 * (n + 1) - 1) :: used n

/-- Row `a` of the table (A003156), for `n ≥ 1`. -/
def rowA (n : ℕ) : ℕ := mex (used (n - 1))

/-- A003157: row `b` of the table, `b(n) = a(n) + 2n`, for `n ≥ 1`. -/
def b (n : ℕ) : ℕ := rowA n + 2 * n

/-- Kimberling's conjecture: `A003157(n) / n → 4`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (b n : ℝ) / n) Filter.atTop (nhds 4) := by
  sorry

end OMA.S_oeis_a003157
