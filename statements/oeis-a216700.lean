import Mathlib

/-!
# A216700: Violations of Rosser's rule; Lehman's conjecture that the first one exceeds 10^7

Source: https://oeis.org/A216700
Credit: @Solfanbtc

A216700 lists the numbers `n` such that the Gram block `[g(n), g(n+k))` contains fewer than `k`
points `t` with `Z(t) = 0`, where `Z` is the Riemann-Siegel Z-function. A Gram block
`[g(m), g(m+k))` is a half-open interval where `g(m)` and `g(m+k)` are good Gram points and
`g(m+1), …, g(m+k-1)` are bad Gram points; `g(n)` is good if `(-1)^n Z(g(n)) > 0`, bad otherwise.

The entry says: "Lehman showed that this sequence is infinite and conjectured (correctly) that
a(1) > 10^7." Status: solved; Brent (Math. Comp. 33, 1979) found the first violation,
a(1) = 13999525. Since the sequence is infinite, a(1) is its least element, so `main` states:
every violation of Rosser's rule has index greater than `10^7`.

Definitions.
* Riemann-Siegel theta: `θ(t) = Im log Γ(1/4 + it/2) - (t/2) log π` with the continuous branch,
  `θ(0) = 0`. We write it without a complex log-gamma, as
  `θ(t) = ∫_0^t Re ψ(1/4 + is/2) / 2 ds - (t/2) log π`, with `ψ = Γ'/Γ` (indeed
  `d/dt Im log Γ(1/4 + it/2) = Re ψ(1/4 + it/2) / 2`, and `Γ(1/4) > 0`).
* `Z(t) = Re (exp(iθ(t)) ζ(1/2 + it))` (this product is real for real `t`).
* Gram points: `g(n)` (for `n ≥ 0`) is the solution of `θ(t) = nπ` with `t ≥ 7`. `θ` is
  increasing for `t ≥ 6.29`, and `g(-1) ≈ 9.67`, `g(0) ≈ 17.85`, so this solution is unique;
  we only use the predicate `IsGram n t`.
* Zeros: since `|Z(t)| = |ζ(1/2 + it)|`, the points `t` with `Z(t) = 0` are those with
  `ζ(1/2 + it) = 0`; points are counted without multiplicity, as in the source.
-/

namespace OMA.S_oeis_a216700

open Complex

/-- The digamma function `ψ = Γ'/Γ`. -/
noncomputable def psi (z : ℂ) : ℂ := deriv Gamma z / Gamma z

/-- The Riemann-Siegel theta function. -/
noncomputable def theta (t : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..t, (psi (1 / 4 + (s / 2 : ℝ) * I)).re / 2) - t * Real.log Real.pi / 2

/-- The Riemann-Siegel Z-function. -/
noncomputable def Z (t : ℝ) : ℝ :=
  (cexp ((theta t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)).re

/-- `t` is the Gram point `g(n)`. -/
def IsGram (n : ℕ) (t : ℝ) : Prop := 7 ≤ t ∧ theta t = n * Real.pi

/-- The Gram point `g(n) = t` is good. -/
def IsGood (n : ℕ) (t : ℝ) : Prop := 0 < (-1 : ℝ) ^ n * Z t

/-- `n` violates Rosser's rule: for some `k ≥ 1`, `[g(n), g(n+k))` is a Gram block containing
fewer than `k` points `t` with `Z(t) = 0`. Here `g j` stands for `g(n+j)`. -/
def RosserViolation (n : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∃ g : ℕ → ℝ, (∀ j ≤ k, IsGram (n + j) (g j)) ∧
    IsGood n (g 0) ∧ IsGood (n + k) (g k) ∧
    (∀ j, 0 < j → j < k → ¬ IsGood (n + j) (g j)) ∧
    {t : ℝ | g 0 ≤ t ∧ t < g k ∧ riemannZeta (1 / 2 + (t : ℂ) * I) = 0}.ncard < k

/-- Lehman's conjecture (proved: a(1) = 13999525, Brent 1979): every violation of Rosser's rule
has index greater than `10^7`. -/
theorem main : ∀ n : ℕ, RosserViolation n → 10 ^ 7 < n := by
  sorry

end OMA.S_oeis_a216700
