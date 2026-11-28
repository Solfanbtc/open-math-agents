import Mathlib

/-!
# A004081: positive integers `m` with exactly one integer between `exp(H_m)` and `exp(H_{m+1})`

Source: https://oeis.org/A004081
Credit: @Solfanbtc

`a(n)` is the `n`-th positive integer `m` such that only one integer lies between
`exp(s(m))` and `exp(s(m+1))`, where `s(m) = 1 + 1/2 + ... + 1/m` (Mathlib's `harmonic m`).
Equivalently (Kimberling): exactly one integer `k` satisfies `s(m) < log k < s(m+1)`.
Data: 4, 8, 13, 17, 22, 26, 31, ... (offset 1).

Conjecture (David W. Cantrell, Aug 11 2007):
`a(n) = floor(n/(2 - exp(γ)) - 1/2 + exp(γ)/(24n))` for `n ≥ 1`, `γ` the Euler–Mascheroni constant.

Notes.
* The source says "positive integer", so `m ≥ 1` is required: `m = 0` would otherwise qualify
  (exactly one integer, `2`, lies in `(exp 0, exp 1) = (1, e)`).
* `exp(H_m)` is never an integer for `m ≥ 1` (Lindemann), so open versus half-open intervals
  do not matter; we use the open interval, as in the name.
* `Nat.nth p 0` is the smallest element, so `a n = Nat.nth P (n - 1)`.

Sanity check (python, 50-digit decimals): the predicate reproduces all 44 listed terms, and the
formula agrees with the first 656 terms.
-/

namespace OMA.S_oeis_a004081

/-- `m` is a positive integer with exactly one integer strictly between `exp(H_m)` and
`exp(H_{m+1})`. -/
def P (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃! k : ℤ, Real.exp (harmonic m) < k ∧ (k : ℝ) < Real.exp (harmonic (m + 1))

/-- `a(n)`, the `n`-th term (offset 1) of A004081. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- Cantrell's conjecture for A004081. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = ⌊(n : ℝ) / (2 - Real.exp Real.eulerMascheroniConstant) - 1 / 2 +
      Real.exp Real.eulerMascheroniConstant / (24 * n)⌋ := by
  sorry

end OMA.S_oeis_a004081
