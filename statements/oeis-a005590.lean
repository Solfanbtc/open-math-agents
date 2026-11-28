import Mathlib

/-!
# A005590: a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n).

Source: https://oeis.org/A005590
Credit: @Solfanbtc

Conjecture (Ralf Stephan): a(3n) = 0 iff n is in A003714.

A003714 is the sequence of fibbinary numbers: natural numbers `n ≥ 0` whose binary
representation has no two adjacent 1's, i.e. `n &&& (2 * n) = 0` (it starts 0, 1, 2, 4, 5, 8, ...,
so `n = 0` is included, and indeed a(0) = 0).

The sequence takes negative values (e.g. a(5) = -1), so it is defined with values in `ℤ`.
Checked numerically for all `n < 300000`.
-/

namespace OMA.S_oeis_a005590

/-- OEIS A005590: a(0) = 0, a(1) = 1, a(2n) = a(n), a(2n+1) = a(n+1) - a(n). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then a ((n + 2) / 2)
    else a ((n + 2) / 2 + 1) - a ((n + 2) / 2)
  decreasing_by all_goals omega

/-- OEIS A003714: fibbinary numbers, i.e. no two adjacent 1's in the binary expansion. -/
def IsFibbinary (n : ℕ) : Prop := n &&& (2 * n) = 0

theorem main : ∀ n : ℕ, a (3 * n) = 0 ↔ IsFibbinary n := by
  sorry

end OMA.S_oeis_a005590
