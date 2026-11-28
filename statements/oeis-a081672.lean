import Mathlib

/-!
# A081672: Expansion of exp(2x) - exp(0) + BesselI_0(2x).

Source: https://oeis.org/A081672
Credit: @Solfanbtc

`a(n)` is `n!` times the coefficient of `x^n` in `exp(2x) - 1 + I_0(2x)`. Since
`exp(2x) = ∑ 2^n x^n / n!` and `I_0(2x) = ∑_k x^(2k) / (k!)^2`, this is
`a(n) = 2^n - [n = 0] + [n even] · binom(n, n/2)`: 1, 2, 6, 8, 22, 32, 84, ... (checked with
python3 against the 31 listed terms; it is also Irwin's formula in the entry).

Conjecture (R. J. Mathar, 2012): `n a(n) + 2 (1-n) a(n-1) + 4 (1-n) a(n-2) + 8 (n-2) a(n-3) = 0`.
Range fix: the recurrence fails at `n = 3` (the left side is `-8` there, because of the `-1` in
`a(0)`), and python3 confirms it for `4 ≤ n < 500`. So `main` states it for `n ≥ 4`.

Status: proved. R. Israel (2016) notes that the e.g.f. satisfies
`y''' - (2x-2) y'' - (4x+2) y' + (8x-4) y + 8x - 4 = 0`, "which implies Mathar's conjectured
recurrence".
-/

namespace OMA.S_oeis_a081672

/-- `a n = 2^n - [n = 0] + [n even] · binom(n, n/2)`: the coefficients of the e.g.f.
`exp(2x) - 1 + I_0(2x)`. -/
def a (n : ℕ) : ℤ :=
  2 ^ n - (if n = 0 then 1 else 0) + (if Even n then (n.choose (n / 2) : ℤ) else 0)

theorem main :
    ∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * a n + 2 * (1 - (n : ℤ)) * a (n - 1) + 4 * (1 - (n : ℤ)) * a (n - 2) +
        8 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081672
