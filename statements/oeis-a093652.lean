import Mathlib

/-!
# A093652: Let a(1) = 1, a(2) = 2, a(3) = 7, a(4) = 15 and for n >= 5 set a(n) = (n*b(n) - b(n-2)) / 2, where b(n) = 4*b(n-2) - b(n-4) for n >= 5 and b(1) = 1, b(2) = 2, b(3) = 5, b(4) = 8.

Source: https://oeis.org/A093652
Credit: @Solfanbtc

`b` is the auxiliary sequence of the name: `b(1..4) = 1, 2, 5, 8`, `b(n) = 4 b(n-2) - b(n-4)`.
A082630 is the ratio-determined insertion sequence I(7/11) (J. W. Layman, 2003). Start from
`[1, 1]` and repeatedly insert `x + y` between adjacent terms `x, y` whenever `7y ≤ 11x`.
Each initial segment eventually stabilizes, and A082630(n) is the `n`-th entry of all late
stages. `stage s` is the `s`-th stage, and `IsLimitTerm n v` says that its `n`-th entry is
eventually `v`. Checked with python3 (exact arithmetic): the first 25 entries are stable from
stage 35 on, equal the data of A082630 (1, 2, 5, 8, 19, 30, 71, 112, ...), and satisfy the
recurrence of `b`.

Conjecture (in the entry): `b(n) = A082630(n)`. `main` states that every entry of the insertion
process converges and that the `n`-th limit entry is `b(n)`, for all `n ≥ 1`. (Equivalently,
A082630 satisfies `a(n) = 4 a(n-2) - a(n-4)`, a conjecture also listed in A082630. The A082630
statement already in the repository is about different conjectures: the Pell-type, sum and
quotient formulas.)
-/

namespace OMA.S_oeis_a093652

open Filter

/-- `b(1..4) = 1, 2, 5, 8`, `b(n) = 4 b(n-2) - b(n-4)` (over `ℤ`; `b 0` is unused). -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 8
  | n + 5 => 4 * b (n + 3) - b (n + 1)

/-- One insertion pass with ratio `7/11`: insert `x + y` between `x, y` when `7y ≤ 11x`. -/
def ins : List ℕ → List ℕ
  | x :: y :: t => if 7 * y ≤ 11 * x then x :: (x + y) :: ins (y :: t) else x :: ins (y :: t)
  | l => l

/-- The `s`-th stage, starting from `[1, 1]`. -/
def stage : ℕ → List ℕ
  | 0 => [1, 1]
  | s + 1 => ins (stage s)

/-- The `n`-th entry (offset 1) of the stages is eventually `v`. -/
def IsLimitTerm (n v : ℕ) : Prop := ∀ᶠ s in atTop, (stage s)[n - 1]? = some v

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ v : ℕ, IsLimitTerm n v ∧ (v : ℤ) = b n := by
  sorry

end OMA.S_oeis_a093652
