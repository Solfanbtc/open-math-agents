import Mathlib

/-!
# A085376: Ratio-dependent insertion sequence I(0.36704) (see the link below).

Source: https://oeis.org/A085376
Credit: @Solfanbtc

Ratio-determined insertion sequence (J. W. Layman, Ratio-Determined Insertion Sequences and the
Tree of their Recurrence Types, 2003, linked from the entry). Start with `[1, 1]` and repeatedly
form a new sequence by inserting `a + b` between each pair of adjacent terms `a, b` if and only if
`k b ≤ a`, here with `k = 0.36704`. Each initial segment eventually stabilizes, and `I(k)` is the
limit sequence: `a(n)` is the `n`-th entry (offset 1) of all sufficiently late stages.
`stage s` is the `s`-th stage, and `IsLimitTerm n v` says that the `n`-th entry is eventually
`v`. Checked with python3 (exact rationals): the first 25 entries are stable from stage 59 on
and equal the data 1, 3, 11, 30, 109, 297, 1079, ...

Conjecture (in the entry, from Layman's conjecture (C.1) that every RDIS satisfies
`a(n) = C a(n-D) - a(n-2D)`): `a(n) = 10 a(n-2) - a(n-4)`. `main` states that every entry
converges (so the limit sequence is defined) and that the recurrence holds for all `n ≥ 5`.
(python3: it holds for `5 ≤ n ≤ 25`.)
-/

namespace OMA.S_oeis_a085376

open Filter

/-- One insertion pass with ratio `k = 0.36704`. -/
def ins : List ℕ → List ℕ
  | a :: b :: t =>
    if (36704 / 100000 : ℚ) * b ≤ a then a :: (a + b) :: ins (b :: t) else a :: ins (b :: t)
  | l => l

/-- The `s`-th stage, starting from `[1, 1]`. -/
def stage : ℕ → List ℕ
  | 0 => [1, 1]
  | s + 1 => ins (stage s)

/-- The `n`-th entry (offset 1) of the stages is eventually `v`. -/
def IsLimitTerm (n v : ℕ) : Prop := ∀ᶠ s in atTop, (stage s)[n - 1]? = some v

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ v : ℕ, IsLimitTerm n v) ∧
      ∀ n : ℕ, 5 ≤ n → ∀ v v₂ v₄ : ℕ,
        IsLimitTerm n v → IsLimitTerm (n - 2) v₂ → IsLimitTerm (n - 4) v₄ →
          (v : ℤ) = 10 * v₂ - v₄ := by
  sorry

end OMA.S_oeis_a085376
