import Mathlib

/-!
# A007051: the rational recurrence s(n) = (2 s(n-1) + 1)/(s(n-1) + 2) and a(n) = (3^n + 1)/2

Source: https://oeis.org/A007051
Credit: @Solfanbtc

A007051: `a(n) = (3^n + 1)/2` (offset 0). The entry's comment (G. Detlefs, Nov 16 2010):
"It appears that if s(n) is a rational sequence of the form s(1)=2,
s(n) = (2*s(n-1)+1)/(s(n-1)+2), n>1 then s(n)=a(n)/(a(n)-1)."

Status: solved. The entry says "The (corrected) conjecture regarding the sequence s(n) is true
(see Fried link)": S. Fried, Proof of a conjecture stated in A007051, 2025.
The comment as now worded is checked exactly (with python3 `fractions`) for `1 ≤ n < 60`, and
`main` states it for every `n ≥ 1`. Note `a(n) - 1 = (3^n - 1)/2 ≠ 0` for `n ≥ 1`, and
`s(n-1) + 2 > 0` along the recurrence, so no division by zero occurs.
-/

namespace OMA.S_oeis_a007051

/-- A007051 as rationals: `a(n) = (3^n + 1)/2`. -/
def a (n : ℕ) : ℚ := (3 ^ n + 1) / 2

/-- Detlefs' sequence, shifted: `sAux m = s(m+1)`, so `sAux 0 = s(1) = 2`. -/
def sAux : ℕ → ℚ
  | 0 => 2
  | m + 1 => (2 * sAux m + 1) / (sAux m + 2)

/-- `s(n)` for `n ≥ 1` (with the junk value `s(0) = 2`). -/
def s (n : ℕ) : ℚ := sAux (n - 1)

/-- Detlefs' conjecture (proved by S. Fried): `s(n) = a(n)/(a(n) - 1)` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → s n = a n / (a n - 1) := by
  sorry

end OMA.S_oeis_a007051
