import Mathlib

/-!
# A127728: Sum of squared coefficients of q in the q-factorials.

Source: https://oeis.org/A127728
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, Oct 22 2020, %F line of A127728):
`a(n) ~ 6 * sqrt(Pi) * n^(2n - 1/2) / exp(2n)`.

Definitions.
* The q-factorial `faq(n) = Product_{k=1..n} (1 - q^k)/(1 - q) = Product_{k=1..n} (1 + q + ... + q^(k-1))`
  (`faq(0) = 1`), a polynomial in `q` of degree `n(n-1)/2`; `a(n)` is the sum of the squares of
  its coefficients (e.g. `faq(4) = 1 + 3q + 5q^2 + 6q^3 + 5q^4 + 3q^5 + q^6`, `a(4) = 106`).
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`; `n^(2n - 1/2)` is the real power.

Checked with python3: the definition reproduces all listed %S/%T/%U terms, and the ratio of
`a(n)` to the conjectured asymptotic is `0.9688, 0.9864, 0.9930, 0.9953` at `n = 20, 50, 100, 150`.
-/

namespace OMA.S_oeis_a127728

open Asymptotics Filter Polynomial

/-- The q-factorial `Product_{k=1..n} (1 + q + ... + q^(k-1))`. -/
noncomputable def faq (n : ℕ) : ℕ[X] := ∏ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), X ^ i

/-- A127728: the sum of the squared coefficients of `faq n` (degree `n(n-1)/2`). -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n * (n - 1) / 2 + 1), (faq n).coeff k ^ 2

/-- Kotesovec's conjecture: `a(n) ~ 6 √π n^(2n - 1/2) e^(-2n)`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => 6 * Real.sqrt Real.pi * (n : ℝ) ^ (2 * (n : ℝ) - 1 / 2) / Real.exp (2 * n)) := by
  sorry

end OMA.S_oeis_a127728
