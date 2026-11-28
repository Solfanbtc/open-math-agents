import Mathlib

/-!
# A061871: |First digit - second digit + third digit - fourth digit ...| = 2

Source: https://oeis.org/A061871
Credit: @Solfanbtc

The positive integers `m` whose alternating digit sum (in decimal) has absolute value `2`:
`2, 13, 20, 24, 31, 35, …` (offset 1); `a(n)` is the `n`-th of them. The absolute value does not
depend on whether the alternation starts from the first or the last digit, so the digits are
taken least significant first (`Nat.digits`). This reproduces all 55 data terms.

Conjecture (Charles R Greathouse IV, Jan 01 2026, OEIS formula): `a(n) ~ k n √(log n)` for some
`k`. ("Possibly the constant is `√(1650π)/(18√(log 10))`" is only suggested, and is not stated.)
Stated as: there is a real `k` with `a(n) ~ k n √(log n)` (`Asymptotics.IsEquivalent`; such a `k`
is necessarily positive).
-/

namespace OMA.S_oeis_a061871

/-- Alternating sum of a digit list: `d₀ - d₁ + d₂ - ⋯`. -/
def altSum : List ℕ → ℤ
  | [] => 0
  | d :: l => d - altSum l

/-- `m` is a term: `m ≥ 1` and its alternating digit sum is `±2`. -/
def IsTerm (m : ℕ) : Prop := 1 ≤ m ∧ |altSum (Nat.digits 10 m)| = 2

/-- A061871 (offset 1): the `n`-th term. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Greathouse's conjecture: `a(n) ~ k n √(log n)` for some `k`. -/
theorem main : ∃ k : ℝ, Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => k * n * Real.sqrt (Real.log n)) := by
  sorry

end OMA.S_oeis_a061871
