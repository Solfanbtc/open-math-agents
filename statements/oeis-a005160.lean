import Mathlib

/-!
# A005160: Number of alternating sign n X n matrices invariant under a quarter turn.

Source: https://oeis.org/A005160
Credit: @Solfanbtc

The OEIS entry says: "Robbins gives a simple (conjectured) formula". The formula is the one from
D. P. Robbins, *Symmetry classes of alternating-sign matrices* (arXiv:math/0008045), relating the
number `A_QT(m)` of quarter-turn symmetric `m × m` alternating sign matrices to the number
`A_HT(m)` of half-turn symmetric ones and the number `A(m)` of all of them:

* `A_QT(4n)     = A_HT(2n)     · A(n)^2`
* `A_QT(4n + 1) = A_HT(2n + 1) · A(n)^2`
* `A_QT(4n + 2) = 0`
* `A_QT(4n + 3) = A_HT(2n + 1) · A(n + 1)^2`   (Robbins writes this as `A_QT(4n - 1)`, `n ≥ 1`)

(The even case was proved by Kuperberg, the odd cases by Razumov and Stroganov.)

Checked by brute force for `m ≤ 12`: `A_QT = 1, 0, 1, 2, 3, 0, 12, 40, 100, 0, 1225, 6860` for
`m = 1..12`,
with `A_HT = 1, 2, 3, 10, 25, 140, 588` for `m = 1..7` and `A = 1, 1, 2, 7` for `m = 0..3`.

Conventions: an `m × m` alternating sign matrix has entries in `{-1, 0, 1}`, every row and column
sums to `1`, and every prefix sum of a row or column lies in `{0, 1}` (equivalently, the nonzero
entries of each row and column alternate in sign). The quarter turn sends `A` to the matrix
`(i, j) ↦ A (m-1-j) i`; half turn sends it to `(i, j) ↦ A (m-1-i) (m-1-j)`. The empty `0 × 0`
matrix counts as one alternating sign matrix (`A(0) = A_HT(0) = A_QT(0) = 1`).
-/

namespace OMA.S_oeis_a005160

open Finset

/-- `A` is an alternating sign matrix. -/
def IsASM {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  (∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) ∧
  (∀ i, ∑ j, A i j = 1) ∧
  (∀ j, ∑ i, A i j = 1) ∧
  (∀ i k : Fin m, (∑ j ∈ Iic k, A i j = 0 ∨ ∑ j ∈ Iic k, A i j = 1)) ∧
  (∀ j k : Fin m, (∑ i ∈ Iic k, A i j = 0 ∨ ∑ i ∈ Iic k, A i j = 1))

/-- `A` is invariant under a quarter turn: `A i j = A (m-1-j) i`. -/
def IsQuarterTurnSymm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ i j, A i j = A j.rev i

/-- `A` is invariant under a half turn: `A i j = A (m-1-i) (m-1-j)`. -/
def IsHalfTurnSymm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  ∀ i j, A i j = A i.rev j.rev

/-- `A(m)`: the number of `m × m` alternating sign matrices (A005130). -/
noncomputable def asmCount (m : ℕ) : ℕ :=
  {A : Matrix (Fin m) (Fin m) ℤ | IsASM A}.ncard

/-- `A_HT(m)`: the number of half-turn symmetric `m × m` alternating sign matrices (A005158). -/
noncomputable def htCount (m : ℕ) : ℕ :=
  {A : Matrix (Fin m) (Fin m) ℤ | IsASM A ∧ IsHalfTurnSymm A}.ncard

/-- `A_QT(m)` = A005160(m): the number of quarter-turn symmetric `m × m` alternating sign
matrices. -/
noncomputable def qtCount (m : ℕ) : ℕ :=
  {A : Matrix (Fin m) (Fin m) ℤ | IsASM A ∧ IsQuarterTurnSymm A}.ncard

/-- Robbins' formula for the number of quarter-turn symmetric alternating sign matrices. -/
theorem main : ∀ n : ℕ,
    qtCount (4 * n) = htCount (2 * n) * asmCount n ^ 2 ∧
    qtCount (4 * n + 1) = htCount (2 * n + 1) * asmCount n ^ 2 ∧
    qtCount (4 * n + 2) = 0 ∧
    qtCount (4 * n + 3) = htCount (2 * n + 1) * asmCount (n + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a005160
