import Mathlib

/-!
# A097945: a(n) = μ(n) φ(n), and the vanishing of ∑ μ(n)/φ(n)^z

Source: https://oeis.org/A097945
`a(n) = μ(n) φ(n)` (Möbius function times Euler's totient), offset 1.
The entry's comment states two conjectures:
1. "Sum_{n>=1} mu(n)/phi(n) = Sum_{n>=1} a(n)/phi(n)^2 = 0."
2. "Sum_{n>=1} mu(n)/phi(n)^z = 0 for Re(z) > 1."
(The comment also sketches why `∑ μ(n)/φ(n)^s = 0` for real `s > 1`: for odd squarefree `m`,
`φ(2m) = φ(m)` and `μ(2m) = -μ(m)`.)

Conventions.
* In claim 1 the series `∑ μ(n)/φ(n)` does not converge absolutely (`∑ |μ(n)|/φ(n)` diverges),
  so `Sum_{n>=1}` is read as the limit of the partial sums `∑_{n=1}^{N}` as `N → ∞`; both series
  of claim 1 are stated this way, as in the source.
* In claim 2 the series converges absolutely for `Re z > 1`, and we state it with `HasSum`
  (unconditional convergence to 0), which is then the same as convergence of the partial sums.
  `φ(n)^z` is the complex power `(φ(n) : ℂ) ^ z`, with `φ(n) ≥ 1` for `n ≥ 1`.
Checked with python3: the listed terms `a(1..26)` agree with `μ(n) φ(n)`; the partial sums of
`μ(n)/φ(n)` are 0.0142, -0.0032, -0.00093, 0.00031 at `N = 10^3, 10^4, 10^5, 10^6`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a097945

open ArithmeticFunction Filter Topology

/-- A097945: `a(n) = μ(n) φ(n)`. -/
def a (n : ℕ) : ℤ := moebius n * (Nat.totient n : ℤ)

theorem main :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (moebius n : ℝ) / (Nat.totient n : ℝ))
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (a n : ℝ) / (Nat.totient n : ℝ) ^ 2)
      atTop (𝓝 0) ∧
    ∀ z : ℂ, 1 < z.re →
      HasSum (fun n : ℕ => (moebius (n + 1) : ℂ) / (Nat.totient (n + 1) : ℂ) ^ z) 0 := by
  sorry

end OMA.S_oeis_a097945
