import Mathlib

/-!
# A109134: Kimberling's ratio limits L(r) for 1/Sum floor((k+1) r) (-x)^k tend to Φ as r → 5/3⁻

Source: https://oeis.org/A109134
Credit: @Solfanbtc

A109134: the decimal expansion of `Φ = 1.7548776662…`, the real root of `1/x = (x - 1)^2`
(equivalently of `x^3 - 2x^2 + x - 1 = 0`).

Conjectures (C. Kimberling, Jul 11 2017): "Suppose that r is a real number in the interval
[3/2, 5/3). Let C(r) = (c(k)) be the sequence of coefficients in the Maclaurin series for
1/(Sum_{k>=0} floor((k+1)*r))(-x)^k). Conjectures: the limit L(r) of c(k+1)/c(k) as k -> oo
exists, L(r) is discontinuous at 5/3 (cf. A279676), and the left limit of L(r) as r->5/3 is
Phi."

What is stated. `main` states the two precise parts: for every `r ∈ [3/2, 5/3)` the ratio
`c(k+1)/c(k)` converges to some `L(r)`, and `L(r) → Φ` as `r → 5/3` from the left. The middle
claim is not stated: at `r = 5/3` itself the ratio has no limit (the coefficients, A279676 up to
signs, have g.f. `(1 - x)(1 - x^3)/(1 + 2x + 2x^2)` and oscillate with period 4), so "L is
discontinuous at 5/3" has no precise meaning beyond the left limit `Φ` not being a value of `L`
there. `Φ` is pinned down by the equation `1/Φ = (Φ - 1)^2`, which has exactly one real root.

Checked with python3 (exact rationals, 400 coefficients): the ratio settles at 2 for `r = 3/2`,
1.69562… for `r = 8/5`, 1.76405… for `r = 13/8`, 1.754889 for `r = 1.65`, and 1.7548777 for
`r = 5/3 - 1/1000`; at `r = 5/3` it keeps oscillating.
-/

namespace OMA.S_oeis_a109134

open PowerSeries Filter Topology

/-- `c_r(k)`: the coefficients of `1/(Sum_{k ≥ 0} floor((k+1) r) (-x)^k)`. -/
noncomputable def c (r : ℝ) (k : ℕ) : ℝ :=
  coeff k (PowerSeries.mk (fun j => ((⌊((j : ℝ) + 1) * r⌋ : ℤ) : ℝ) * (-1) ^ j))⁻¹

/-- Kimberling's conjectures (existence of `L(r)` on `[3/2, 5/3)` and its left limit `Φ`). -/
theorem main : ∀ Φ : ℝ, 1 / Φ = (Φ - 1) ^ 2 →
    ∃ L : ℝ → ℝ,
      (∀ r ∈ Set.Ico (3 / 2 : ℝ) (5 / 3),
        Tendsto (fun k : ℕ => c r (k + 1) / c r k) atTop (𝓝 (L r))) ∧
      Tendsto L (𝓝[<] (5 / 3 : ℝ)) (𝓝 Φ) := by
  sorry

end OMA.S_oeis_a109134
