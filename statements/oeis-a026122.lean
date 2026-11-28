import Mathlib

/-!
# A026122: a(n) is the number of (s(0),s(1),...,s(n)) such that every s(i) is a nonnegative integer, s(0) = 1, s(n) = 1, |s(1) - s(0)| = 1, |s(i) - s(i-1)| <= 1 for i >= 2.

Source: https://oeis.org/A026122
Credit: @Solfanbtc

`a(n)` (offset 2) is the number of sequences `(s(0), ..., s(n))` of nonnegative integers with
`s(0) = 1`, `s(n) = 1`, `|s(1) - s(0)| = 1` and `|s(i) - s(i-1)| ≤ 1` for `2 ≤ i ≤ n`:
`a(2) = 2, a(3) = 4, a(4) = 11, a(5) = 28, ...`.

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
`(n+4) a(n) + (-3n-5) a(n-1) + (-n-6) a(n-2) + 3(n-3) a(n-3) = 0`,
stated for all `n ≥ 5` (where `a(n-3)` is in the sequence's range, `n - 3 ≥ 2`).

A python3 check (dynamic programming over the walks): the definition reproduces the data and the
recurrence holds for all `5 ≤ n < 300`.

Conventions: a sequence is a function `Fin (n + 1) → ℕ`; `a(n)` is the cardinality (`Set.ncard`)
of the finite set of admissible sequences (for `n ≥ 1`; index 1 is `⟨1, _⟩`). The recurrence is
stated in `ℤ`.
-/

namespace OMA.S_oeis_a026122

/-- The admissible sequences `(s(0), ..., s(n))` (for `n ≥ 1`). -/
def walks (n : ℕ) (hn : 1 ≤ n) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = 1 ∧ s (Fin.last n) = 1 ∧ |(s ⟨1, by omega⟩ : ℤ) - (s 0 : ℤ)| = 1 ∧
    ∀ i : Fin (n + 1), 2 ≤ i.val → |(s i : ℤ) - (s ⟨i.val - 1, by omega⟩ : ℤ)| ≤ 1}

/-- `a n = A026122(n)` for `n ≥ 2` (`0` for `n = 0`). -/
noncomputable def a (n : ℕ) : ℤ := if hn : 1 ≤ n then ((walks n hn).ncard : ℤ) else 0

/-- Mathar's conjectured recurrence, for all `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 4) * a n + (-3 * (n : ℤ) - 5) * a (n - 1) + (-(n : ℤ) - 6) * a (n - 2)
      + 3 * ((n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026122
