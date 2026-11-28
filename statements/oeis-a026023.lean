import Mathlib

/-!
# A026023: a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n and s(0) = 3.

Source: https://oeis.org/A026023
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of sequences `(s(0), ..., s(n))` of nonnegative integers with
`s(0) = 3` and `|s(i) - s(i-1)| = 1` for `1 ≤ i ≤ n`: `1, 2, 4, 8, 15, 30, 56, ...`.

Conjecture (R. J. Mathar, Sep 29 2012, in the entry):
`(n+4)(n-1) a(n) + (n-1)(n+1) a(n-1) - 2(n+1)(2n+1) a(n-2) - 4(n-1)(n+1) a(n-3) = 0`,
stated for all `n ≥ 3` (where `a(n-3)` is defined).

A python3 check (dynamic programming over the walks): the definition reproduces the data and the
recurrence holds for all `3 ≤ n < 300`.

Conventions: a sequence is a function `Fin (n + 1) → ℕ` (values are nonnegative integers);
`a(n)` is the cardinality (`Set.ncard`) of the finite set of admissible sequences. The recurrence
is stated in `ℤ`.
-/

namespace OMA.S_oeis_a026023

/-- Walks `(s(0), ..., s(n))` on the nonnegative integers with `s(0) = 3` and steps `±1`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | s 0 = 3 ∧ ∀ i : Fin (n + 1), 1 ≤ i.val →
    |(s i : ℤ) - (s ⟨i.val - 1, by omega⟩ : ℤ)| = 1}

/-- `a n = A026023(n)`. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * (n - 1) * a n + ((n : ℤ) - 1) * (n + 1) * a (n - 1)
      - 2 * ((n : ℤ) + 1) * (2 * n + 1) * a (n - 2)
      - 4 * ((n : ℤ) - 1) * (n + 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026023
