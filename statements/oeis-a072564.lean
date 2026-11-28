import Mathlib

/-!
# A072564: Numbers m such that the absolute values of the real and imaginary part of zeta(1/2 + m*i) are both < 1.

Source: https://oeis.org/A072564
Credit: @Solfanbtc

`S` is the set of positive integers `m` with `|Re ζ(1/2 + m i)| < 1` and `|Im ζ(1/2 + m i)| < 1`.
The OEIS offset is 1, so `a n` is the `n`-th element of `S` for `n ≥ 1`, i.e.
`a n = Nat.nth S (n - 1)`. The sequence starts 1, 2, 3, 4, 5, 6, 13, 14, 15, 21, ...
(`m = 0` is not a term either way, since `ζ(1/2) ≈ -1.46`).

Conjecture (B. Cloitre, 2002): `lim_{n → ∞} a(n)/n = C` exists, with `5 < C < 6`.

`main` states exactly this conjecture. The entry itself adds (V. Kotesovec, Feb 18 2021):
"The conjecture was based on erroneous terms; C is about 2.05". So the corrected data suggest that
the statement is false (the bound `5 < C < 6` fails), and it is stated here as the source states it,
as a target for a disproof.
-/

namespace OMA.S_oeis_a072564

open Filter Topology Complex

/-- Positive integers `m` such that `ζ(1/2 + m i)` has real and imaginary parts of absolute
value `< 1`. -/
def S : Set ℕ :=
  {m | 0 < m ∧ |(riemannZeta (1 / 2 + (m : ℂ) * I)).re| < 1 ∧
    |(riemannZeta (1 / 2 + (m : ℂ) * I)).im| < 1}

/-- `a n` is the `n`-th term of A072564 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth S (n - 1)

theorem main :
    ∃ C : ℝ, 5 < C ∧ C < 6 ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a072564
