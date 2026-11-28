import Mathlib

/-!
# A097154: Number of iterations of f(x) = reverse(x) - maxdigit(x) needed to reach zero, or -1 if zero is never reached, where maxdig(n) is the largest digit of n.

Source: https://oeis.org/A097154
Credit: @Solfanbtc

Conjecture (OEIS A097154, %C line): `0` and `89` are the only fixed points of
`f(x) = reverse(x) - maxdigit(x)` (e.g. `f(89) = 98 - 9 = 89`).

Formalization.
* `reverse x` is the number with the decimal digits of `x` in reverse order (leading zeros of
  the reversal dropped, e.g. `reverse 120 = 21`); `maxDigit x` is the largest decimal digit of
  `x` (`0` for `x = 0`).
* `f` is computed in `ℕ`. The subtraction is exact: the largest digit of `x` occurs among the
  digits of `reverse x`, so `reverse x ≥ maxDigit x`.
* The fixed points are taken over all nonnegative integers (the domain of the iteration).

Checked with python3: iterating this `f` reproduces all listed %S/%T/%U terms of A097154
(including `a(89) = -1`), and the only fixed points below `10^7` are `0` and `89`.
-/

namespace OMA.S_oeis_a097154

/-- Decimal reversal. -/
def reverse (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Largest decimal digit (`0` for `0`). -/
def maxDigit (x : ℕ) : ℕ := (Nat.digits 10 x).foldr max 0

/-- `f(x) = reverse(x) - maxdigit(x)`. -/
def f (x : ℕ) : ℕ := reverse x - maxDigit x

/-- The only fixed points of `f` are `0` and `89`. -/
theorem main : ∀ x : ℕ, f x = x ↔ x = 0 ∨ x = 89 := by
  sorry

end OMA.S_oeis_a097154
