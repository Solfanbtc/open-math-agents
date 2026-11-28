import Mathlib

/-!
# A047788: Numerators of Glaisher's I-numbers.

Source: https://oeis.org/A047788
Credit: @Solfanbtc

Glaisher's I-numbers `I(n) = A047788(n) / A047789(n)` (offset 0, in lowest terms) are
`I(n) = (2n)! · [x^{2n}] 3/(2 + 4 cos x)` (the entry's Maple program; equivalently the e.g.f. of
`(-1)ⁿ I(n)` is `(3/2)/(1 + 2 cosh x)`): `1/2, 1/3, 1, 7, 809/9, 1847, 55601, ...`.

Conjecture (Jianing Song, Nov 17 2019, in the entry):
`L(2n+1, χ₃) = I(n) · (2π)^{2n+1} / ((2n)! · 3^{2n + 3/2})`, where
`L(s, χ₃) = ∑_{k ≥ 1} (k/3)/k^s` is the Dirichlet L-function of the non-principal character
modulo 3 (`(k/3)` the Legendre symbol: `0` if `3 ∣ k`, `1` if `k ≡ 1`, `-1` if `k ≡ 2 (mod 3)`).
Stated for every `n ≥ 0`.

A python3 check: the series reproduces `I(0), ..., I(7)` from the data, and both sides agree to
about 15 digits for `n = 1, ..., 6` (and `n = 0` gives the classical `L(1, χ₃) = π/(3√3)`).

Conventions:
* `I(n)` is used directly as a rational number (`A047788(n)/A047789(n)` is its reduced form).
  The series `3/(2 + 4 cos x)` is computed in `ℚ⟦X⟧` with `PowerSeries.cos`.
* `L(2n+1, χ₃)` is the limit of the partial sums `∑_{k=1}^{N}` (for `n = 0` the series converges
  only conditionally). `3^{2n+3/2} = 3^{2n} · 3√3`.
-/

namespace OMA.S_oeis_a047788

open PowerSeries Filter Topology

/-- Glaisher's `I(n) = (2n)! [x^{2n}] 3/(2 + 4 cos x)`. -/
noncomputable def glaisherI (n : ℕ) : ℚ :=
  ((2 * n).factorial : ℚ) * coeff (2 * n) (C (3 : ℚ) * (C (2 : ℚ) + C (4 : ℚ) * cos ℚ)⁻¹)

/-- The non-principal character modulo 3 (Legendre symbol `(k/3)`). -/
def χ₃ (k : ℕ) : ℤ := if k % 3 = 0 then 0 else if k % 3 = 1 then 1 else -1

/-- Song's conjecture: `L(2n+1, χ₃) = I(n) (2π)^{2n+1} / ((2n)! 3^{2n+3/2})`. -/
theorem main : ∀ n : ℕ,
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (χ₃ k : ℝ) / (k : ℝ) ^ (2 * n + 1)) atTop
      (𝓝 ((glaisherI n : ℝ) * (2 * Real.pi) ^ (2 * n + 1) /
        (((2 * n).factorial : ℝ) * 3 ^ (2 * n) * (3 * Real.sqrt 3)))) := by
  sorry

end OMA.S_oeis_a047788
