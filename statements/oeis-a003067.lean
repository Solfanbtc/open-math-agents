import Mathlib

/-!
# A003067: Problimes (second definition).

Source: https://oeis.org/A003067
Credit: @Solfanbtc

Claim (OEIS A003067, comment): the g.f. (z^2+2+z^9+z^5)/(z-1)^2 conjectured by Simon
Plouffe in his 1992 dissertation is wrong.

STATUS: the entry states that Plouffe's conjectured generating function is wrong; the
statement below is that refutation: it is not the case that a(n+1) is the coefficient of
z^n in (2 + z^2 + z^5 + z^9)/(1 - z)^2 for every n (offset 1, so a(1) = 2 is the constant
coefficient).

Definitions:
* a(1) = 2 and a(i+1) = round(a(i) + 1/Product_{j=1..i} (1 - 1/a(j))) (Maple and Mathematica
  programs of the entry), rounded to the nearest integer and to the even one in case of a
  tie (comment of Michael B. Porter). `state n = (a(n+1), Product_{j=1..n+1} (1 - 1/a(j)))`.
* Checked in Python with exact rationals: this reproduces all 57 listed terms (no tie
  occurs among the first 80 terms), and the coefficients of the g.f. agree with
  a(1), ..., a(20) but differ from a(21) = 90 onwards.
-/

namespace OMA.S_oeis_a003067

open PowerSeries

/-- Rounding to the nearest integer, ties to the even integer. -/
def roundHalfEven (x : ℚ) : ℤ :=
  if x - ⌊x⌋ = 1 / 2 then (if Even ⌊x⌋ then ⌊x⌋ else ⌊x⌋ + 1) else round x

/-- `state n = (a(n+1), ∏_{j ≤ n+1} (1 - 1/a(j)))`. -/
def state : ℕ → ℤ × ℚ
  | 0 => (2, 1 - 1 / 2)
  | n + 1 =>
      let y := roundHalfEven ((state n).1 + 1 / (state n).2)
      (y, (state n).2 * (1 - 1 / (y : ℚ)))

/-- A003067(n) for `n ≥ 1`. -/
def a (n : ℕ) : ℤ := (state (n - 1)).1

/-- Plouffe's conjectured generating function `(2 + z^2 + z^5 + z^9)/(1 - z)^2`. -/
noncomputable def plouffeGF : PowerSeries ℚ := (2 + X ^ 2 + X ^ 5 + X ^ 9) * ((1 - X) ^ 2)⁻¹

/-- Plouffe's conjectured g.f. is wrong. -/
theorem main : ¬ ∀ n : ℕ, ((a (n + 1) : ℤ) : ℚ) = coeff n plouffeGF := by
  sorry

end OMA.S_oeis_a003067
