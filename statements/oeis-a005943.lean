import Mathlib

/-!
# A005943: Factor complexity (number of subwords of length n) of the Golay-Rudin-Shapiro binary word A020987.

Source: https://oeis.org/A005943
Credit: @Solfanbtc

`a n` is the number of distinct subwords (factors) of length `n` of the zero-one
Golay-Rudin-Shapiro word A020987 (offset 0): `w k` is the parity of the number of
(possibly overlapping) occurrences of `11` in the binary expansion of `k`, i.e. the number
of positions `i` with bits `i` and `i + 1` of `k` both set. The empty word is counted, so
`a 0 = 1`, as in the OEIS data.

Conjecture (Joerg Arndt, 2012; checked by Sean A. Irvine for `a(0..63)`): the generating
function of `a` is `(1 + x^2 + 2x^3 + 4x^4 + 4x^6 - 2x^7 - 2x^9) / (1 - x)^2`.
It is stated below as the power-series identity
`(1 - X)^2 · ∑ a n X^n = 1 + X^2 + 2X^3 + 4X^4 + 4X^6 - 2X^7 - 2X^9` over `ℤ`.

Small cases checked numerically: both sides give
`1, 2, 4, 8, 16, 24, 36, 46, 56, 64, 72, 80, …` for `n ≤ 15`.
-/

namespace OMA.S_oeis_a005943

/-- The zero-one Golay-Rudin-Shapiro word A020987: `true` iff the number of positions `i`
with bits `i` and `i + 1` of `k` both equal to `1` is odd (bits at `i ≥ k` vanish). -/
def w (k : ℕ) : Bool :=
  decide (Odd ((Finset.range k).filter (fun i => k.testBit i ∧ k.testBit (i + 1))).card)

/-- The factor complexity of `w`: the number of distinct length-`n` subwords of `w`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {u : Fin n → Bool | ∃ i : ℕ, ∀ j : Fin n, w (i + j) = u j}

/-- Arndt's conjectured generating function for A005943. -/
theorem main :
    (1 - PowerSeries.X) ^ 2 * PowerSeries.mk (fun n => (a n : ℤ)) =
      (1 + PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 + 4 * PowerSeries.X ^ 4 +
        4 * PowerSeries.X ^ 6 - 2 * PowerSeries.X ^ 7 - 2 * PowerSeries.X ^ 9 :
          PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a005943
