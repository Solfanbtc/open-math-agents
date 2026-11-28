import Mathlib

/-!
# A360923: Integer Lunar Lander

Source: https://oeis.org/A360923
Credit: @Solfanbtc

A position is an ordered pair `(i, j)` of integers (velocity, altitude; negative values allowed,
no crash detection). There are always 3 legal moves, to `(i+1, j+i+1)`, `(i, j+i)` and
`(i-1, j+i-1)`. `T(i, j)` (`i, j ≥ 0`) is the smallest number of moves needed to reach `(0, 0)`
from `(i, j)`. Upper left corner (rows `i`): `0 2 3 4 4 5 / 1 3 4 5 5 / 4 5 6 6 / 7 7 8 / ...`.

The entry states two conjectures (N. J. A. Sloane, 2023):
* Conjecture 1: for all `i, j`, `T(i, j)` differs from its eight neighbors by at most 3; with
  the correction by M. F. Hasler (2023), "Conjecture 1 seems to hold for all `(i, j)` except
  `(1, 0)` and `(2, 1)`" (indeed `T(1, 0) = 1` and `T(2, 1) = 5` are neighbors). We state the
  corrected form: for every cell `(i, j)` of the table other than `(1, 0)` and `(2, 1)`, every
  neighboring cell `(i', j')` of the table (`i', j' ≥ 0`, `|i - i'| ≤ 1`, `|j - j'| ≤ 1`,
  `(i', j') ≠ (i, j)`) has `|T(i, j) - T(i', j')| ≤ 3`.
* Conjecture 2: `T(0, j) = 1 + ⌊√(4j - 3)⌋` for `j > 0`, and `T(i, j) = T(0, j + t_{i-1}) + i`
  for `i > 0`, `t_k = k(k+1)/2`. (The consequence for the leading column `T(i, 0)` that the entry
  derives is not stated separately.)
`main` is the conjunction of the two.

`T` is defined as the least `n` such that `(0, 0)` is reachable in exactly `n` moves (`sInf`);
every position of the table is expected to be able to reach `(0, 0)` (Conjecture 2 gives the
finite values). Checks (python3, breadth-first search from `(0, 0)` over the reversed moves): the
first 78 terms of the data are reproduced (antidiagonals read with `i` increasing), and for
`i, j < 24` the only violators of Conjecture 1 are `(1, 0)` and `(2, 1)`, and Conjecture 2 holds.
-/

namespace OMA.S_oeis_a360923

/-- One move of Integer Lunar Lander from `p` to `q`. -/
def Step (p q : ℤ × ℤ) : Prop :=
  (q.1 = p.1 + 1 ∨ q.1 = p.1 ∨ q.1 = p.1 - 1) ∧ q.2 = p.2 + q.1

/-- `(0, 0)` is reached from `p` in exactly `n` moves. -/
def Reach : ℕ → ℤ × ℤ → Prop
  | 0, p => p = (0, 0)
  | n + 1, p => ∃ q, Step p q ∧ Reach n q

/-- `T(i, j)`: the smallest number of moves from `(i, j)` to `(0, 0)`. -/
noncomputable def T (i j : ℕ) : ℕ := sInf {n | Reach n ((i : ℤ), (j : ℤ))}

/-- Conjecture 1 (with Hasler's two exceptions) and Conjecture 2. -/
theorem main :
    (∀ i j i' j' : ℕ, (i, j) ≠ (1, 0) → (i, j) ≠ (2, 1) → (i', j') ≠ (i, j) →
      |(i : ℤ) - i'| ≤ 1 → |(j : ℤ) - j'| ≤ 1 → |(T i j : ℤ) - T i' j'| ≤ 3) ∧
    ((∀ j : ℕ, 0 < j → T 0 j = 1 + Nat.sqrt (4 * j - 3)) ∧
      ∀ i j : ℕ, 0 < i → T i j = T 0 (j + (i - 1) * i / 2) + i) := by
  sorry

end OMA.S_oeis_a360923
