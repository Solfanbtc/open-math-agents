import Mathlib

/-!
# A045761: Define polynomials Pn by P0 = 0, P1 = x, P2 = P1 + P0, P3 = P2 * P1, P4 = P3 + P2, etc. alternately adding or multiplying. For even n > 2k, then first k coefficients of Pn remain unchanged and their values are the first k terms of the sequence.

Source: https://oeis.org/A045761 (and https://oeis.org/A268107)
Credit: @Solfanbtc

Conjecture (Jean-François Alcover, Aug 08 2016, in A045761; restated in A268107): `1/d = λ`,
where `a(n) ~ c * d^n / n^(3/2)` (so `1/d` is the radius of convergence of `Σ a(n) x^n`), and
`λ = 0.39952466709679946...` (A268107) is the Somos quadratic recurrence constant (Finch,
Mathematical Constants, 6.10): for the sequence `h_0 = 0, h_1 = k,
h_n = h_(n-1) * (1 + h_(n-1) - h_(n-2))`, if `k < λ` it converges to a limit less than `1`, and
if `k > λ` it diverges to infinity. A268107's formula: "lambda is the radius of convergence of
the function Sum_{n>=0} A045761(n)*x^n".

Formalization. `P (2n) = P (2n-1) + P (2n-2)`, `P (2n+1) = P (2n) * P (2n-1)` over `ℕ[X]`.
Coefficient `j` of `P m` is stable for even `m > 2(j+1)`; we take `a(j) = coeff (P (2j+4)) j`
(python3 check: this gives the 19 first data terms, and equals coeff `j` of `P m` for all even
`m ≥ 2j+4` tested). `main` says there is a real `λ` that is the Somos threshold (for
`0 < k < λ`, `h` tends to a limit `< 1`; for `k > λ`, `h → ∞`) and is also the radius of
convergence of `Σ a(n) x^n` (summable for `0 < x < λ`, not summable for `x > λ`). Such a `λ`
is unique, so this is exactly `1/d = λ`.
-/

namespace OMA.S_oeis_a045761

open Polynomial Filter

/-- The polynomials `P_n`: `P0 = 0`, `P1 = x`, then alternately adding (even `n`) and
multiplying (odd `n`) the two previous ones. -/
noncomputable def P : ℕ → ℕ[X]
  | 0 => 0
  | 1 => X
  | n + 2 => if (n + 2) % 2 = 0 then P (n + 1) + P n else P (n + 1) * P n

/-- A045761(j): the stable `j`-th coefficient of the even polynomials. -/
noncomputable def a (j : ℕ) : ℕ := (P (2 * j + 4)).coeff j

/-- Somos' quadratic recurrence `h_0 = 0, h_1 = k, h_n = h_(n-1) (1 + h_(n-1) - h_(n-2))`. -/
noncomputable def h (k : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => k
  | n + 2 => h k (n + 1) * (1 + h k (n + 1) - h k n)

/-- Alcover's conjecture: the radius of convergence `1/d` of `Σ a(n) x^n` is Somos' `λ`. -/
theorem main :
    ∃ lam : ℝ,
      (∀ k : ℝ, 0 < k → k < lam → ∃ L : ℝ, L < 1 ∧ Tendsto (h k) atTop (nhds L)) ∧
      (∀ k : ℝ, lam < k → Tendsto (h k) atTop atTop) ∧
      (∀ x : ℝ, 0 < x → x < lam → Summable (fun n => (a n : ℝ) * x ^ n)) ∧
      (∀ x : ℝ, lam < x → ¬ Summable (fun n => (a n : ℝ) * x ^ n)) := by
  sorry

end OMA.S_oeis_a045761
