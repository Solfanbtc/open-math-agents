import Mathlib

/-!
# A133361: Multiply by 9 and reverse.

Source: https://oeis.org/A133361
Credit: @Solfanbtc

Claim (entry formula, conjectured by Vaclav Kotesovec, 2020): a(n)^(1/n) → 10 as n → ∞.

Definition: a(1) = 1 and a(n) = reverse(9·a(n-1)), where reverse reverses the decimal digits
(leading zeros of the reversal are dropped, as in the entry's Maple and Mathematica programs).
The offset is 1; `a 0` is set to 0 only to make the function total and does not affect the limit.
`#eval` reproduces the listed terms 1, 9, 18, 261, 9432, 88848, 236997, ...
-/

namespace OMA.S_oeis_a133361

/-- Decimal digit reversal. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- A133361(n) for n ≥ 1. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => rev (9 * a (n + 1))

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) Filter.atTop (nhds 10) := by
  sorry

end OMA.S_oeis_a133361
