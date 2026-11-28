import Mathlib

/-!
# A013663: Bala's conjectured family of rapidly converging series for zeta(5)

Source: https://oeis.org/A013663
Credit: @Solfanbtc

A013663 is the decimal expansion of `zeta(5)`. The entry records (P. Bala, Oct 29 2023):
`zeta(5) = 131/128 + 26 * Sum_{n >= 1} (n^2 + 2n + 40/39)/(n(n+1)(n+2))^5` and
`zeta(5) = 5162893/4976640 - 1323520 * Sum_{n >= 1} (n^2 + 4n + 56288/12925)/(n(n+1)⋯(n+4))^5`,
and then:

  "Conjecture: for k >= 1, there exist rational numbers A(k), B(k) and c(k) such that
  zeta(5) = A(k) + B(k)*Sum_{n >= 1} (n^2 + 2*k*n + c(k))/(n*(n + 1)*...*(n + 2*k))^5."

`main` states this for every `k ≥ 1`. The cases `k = 1, 2` above were checked numerically with
python3. The sum over `n ≥ 1` is written as a sum over `m : ℕ` with `n = m + 1`; it converges
absolutely (its terms are `O(n^(2 - 5(2k+1)))`), so `tsum` is the usual sum.
The entry's remark that "a similar conjecture can be made for the constant zeta(3)" is not
spelled out there and is not stated here.
-/

namespace OMA.S_oeis_a013663

/-- `Sum_{n >= 1} (n^2 + 2kn + c)/(n(n+1)⋯(n+2k))^5`. -/
noncomputable def series (k : ℕ) (c : ℚ) : ℝ :=
  ∑' m : ℕ, (((m + 1 : ℝ) ^ 2 + 2 * k * (m + 1) + c) /
    (∏ j ∈ Finset.range (2 * k + 1), ((m + 1 + j : ℕ) : ℝ)) ^ 5)

/-- Bala's conjecture: for every `k ≥ 1` there are rationals `A, B, c` with
`zeta(5) = A + B * Sum_{n >= 1} (n^2 + 2kn + c)/(n(n+1)⋯(n+2k))^5`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ A B c : ℚ,
    riemannZeta 5 = (((A : ℝ) + B * series k c : ℝ) : ℂ) := by
  sorry

end OMA.S_oeis_a013663
