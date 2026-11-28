import Mathlib

/-!
# A132411: a(0) = 0, a(1) = 1 and a(n) = n^2 - 1 with n >= 2.

Source: https://oeis.org/A132411 (conjecture by Peter Bala, May 10 2025; OEIS Foundation,
CC BY-SA 4.0).
Credit: @Solfanbtc

Conjecture (OEIS): the sequence terms are the exponents in the expansion of the q-series
  Sum_{n >= 0} q^(2*n) * Product_{k >= 2*n+2} (1 - (-q)^k) = 1 + q^3 + q^8 + q^15 + q^24 + ....

Formalization notes.
* The displayed expansion 1 + q^3 + q^8 + q^15 + ... = Sum_{m >= 1} q^(m^2 - 1) has exponents
  0, 3, 8, 15, 24, ..., i.e. the terms a(n) = n^2 - 1 for n >= 2 together with 0 = a(0); the term
  a(1) = 1 is not an exponent (q^1 does not occur). We state the explicit identity of formal
  power series displayed in the source, with every coefficient: the coefficient of q^N is 1 if
  N + 1 is a perfect square and 0 otherwise. This is the minimal reading consistent with the
  source's own expansion.
* The q-series is a formal power series in q over ℤ. Its coefficient of q^N only involves the
  summands with 2n ≤ N and, in each product, the factors with k ≤ N (a factor 1 - (-q)^k with
  k > N is 1 modulo q^(N+1)). So for each N we compute that coefficient exactly from the
  polynomial truncation Sum_{n ≤ N} q^(2n) Prod_{2n+2 ≤ k ≤ N} (1 - (-q)^k); this is the
  standard meaning of the infinite sum and products as formal power series.
* A python computation confirms the identity for all N ≤ 400.
-/

namespace OMA.S_oeis_a132411

open Polynomial

/-- The truncation at degree N of Sum_{n >= 0} q^(2n) Prod_{k >= 2n+2} (1 - (-q)^k): its
coefficients of q^0, ..., q^N agree with those of the full q-series. -/
noncomputable def truncation (N : ℕ) : ℤ[X] :=
  ∑ n ∈ Finset.range (N + 1),
    X ^ (2 * n) * ∏ k ∈ Finset.Ico (2 * n + 2) (N + 1), (1 - (-X) ^ k)

theorem main : ∀ N : ℕ,
    (truncation N).coeff N = if IsSquare (N + 1) then 1 else 0 := by
  sorry

end OMA.S_oeis_a132411
