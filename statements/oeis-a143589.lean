import Mathlib

/-!
# A143589: Kolakoski fan based on A000034 with initial row 1.

Source: https://oeis.org/A143589
Credit: @Solfanbtc

Claim (entry comment, Clark Kimberling, following Benoit Cloitre's conjecture at A111090): if L(n)
is the number of terms in row n of the fan K (L = A143590), then L(n)·(2/3)^n approaches a
constant. Stated literally: L(n)·(2/3)^n converges to some real number (the source does not
require the constant to be positive).

The fan (from the entry's formula), with s = A000034 = (1, 2, 1, 2, ...) indexed from 1 and
initial row w = (1): row 1 is (1); for n ≥ 2, row n starts with s(n) (1 for odd n, 2 for even n)
and is obtained by Kolakoski substitution from row n-1: the i-th term of row n-1 is the length
(1 or 2) of the i-th run of row n, and runs alternate between 1 and 2. Rows are finite, so L(n)
is finite. These rows are the strings of A111090 (start with 2 after a row starting with 1, and
vice versa). A python check: the rows reproduce all 105 listed terms of A143589 and the 21
listed terms of A143590, and L(n)·(2/3)^n ≈ 0.4094 for 30 ≤ n < 40.
-/

namespace OMA.S_oeis_a143589

/-- Kolakoski substitution: runs of lengths `l`, alternating values, first value `v`. -/
def expand : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: l, v => List.replicate x v ++ expand l (3 - v)

/-- Row `n + 1` of the fan (0-indexed here: `row 0` is row 1 of the entry). -/
def row : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => expand (row n) (if (n + 2) % 2 = 1 then 1 else 2)

/-- L(n) = A143590(n), the length of row n (n ≥ 1). -/
def L (n : ℕ) : ℕ := (row (n - 1)).length

theorem main :
    ∃ c : ℝ, Filter.Tendsto (fun n : ℕ => (L n : ℝ) * (2 / 3) ^ n) Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a143589
