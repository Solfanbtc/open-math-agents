import Mathlib

/-!
# A117231: Decimal expansion of Integral_{x=0..1} cos((log x)/x)/x dx.

Source: https://oeis.org/A117231
Credit: @Solfanbtc

The constant is `c = ∫_0^1 cos((log x)/x)/x dx = 0.32336743167777876139937...` (Trefethen's
challenge, problem 1). The integrand oscillates with amplitude `1/x` near `0`, so it is not
Lebesgue integrable on `(0, 1)`: the integral is the improper one, `lim_{ε → 0+} ∫_ε^1`.

Conjecture (Peter Bala, Dec 28 2022, in the entry; see Finch, *Mathematical Constants*, p. 62):
`c` is the Borel sum of the divergent series `∑_{n ≥ 1} (-1)^(n+1) (2n)^(2n-1)`.

Convention for the Borel sum. With the term `a_n = (-1)^(n+1) (2n)^(2n-1)` weighted by `1/n!`,
the Borel transform `∑ a_n t^n / n!` has radius of convergence `0` (`(2n)^(2n-1)/n!` grows
super-exponentially), so that reading is void. The series arises (substituting `x = e^{-u}`,
`v = u e^u`, `∫_0^∞ cos(v) W'(v) dv` with Lambert `W`, and `∫_0^∞ cos(v) v^m dv ↦ m! Re(i^(m+1))`)
as the value at `z = 1` of the power series `∑ a_n z^(2n-1)`; its Borel transform is
`B(t) = ∑_{n ≥ 1} a_n t^(2n-1)/(2n-1)!`, which converges for `|t| < 1/e`, and the Borel sum is
`∫_0^∞ e^{-t} B(t) dt`, where `B` is continued analytically along `[0, ∞)`.
(Here `B(t) = i (W'(it) - W'(-it))/2`, real for real `t`.)

A python3 check (Newton iteration for `W`, Simpson's rule on `[0, 60]`):
`∫_0^∞ e^{-t} B(t) dt ≈ 0.32336743167758`, agreeing with the constant to about 12 digits,
and the series for `B(0.05)` agrees with the closed form.

Formal statement: there is `f : ℝ → ℝ`, analytic at every point of `[0, ∞)`, equal to the series
`B` on some `[0, r)` with `r > 0` (this determines `f` on `[0, ∞)` by the identity theorem), such
that the improper integral `∫_0^T e^{-t} f(t) dt` (as `T → ∞`) converges to the improper integral
`lim_{ε → 0+} ∫_ε^1 cos((log x)/x)/x dx`.
-/

namespace OMA.S_oeis_a117231

open Filter Topology

/-- The `n`-th term of the series, `n ≥ 1`: `a n = (-1)^(n+1) (2n)^(2n-1)`. -/
def a (n : ℕ) : ℤ := (-1) ^ (n + 1) * (2 * n : ℤ) ^ (2 * n - 1)

/-- Bala's conjecture: the Borel sum of `∑_{n ≥ 1} (-1)^(n+1) (2n)^(2n-1)` equals
`∫_0^1 cos((log x)/x)/x dx` (improper at `0`). -/
theorem main : ∃ f : ℝ → ℝ, AnalyticOnNhd ℝ f (Set.Ici 0) ∧
    (∃ r > 0, ∀ t ∈ Set.Ico (0 : ℝ) r,
      HasSum (fun n : ℕ => (a (n + 1) : ℝ) * t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        (f t)) ∧
    ∃ c : ℝ,
      Tendsto (fun ε : ℝ => ∫ x in ε..1, Real.cos (Real.log x / x) / x) (𝓝[>] 0) (𝓝 c) ∧
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, Real.exp (-t) * f t) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a117231
