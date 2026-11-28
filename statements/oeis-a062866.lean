import Mathlib

/-!
# A062866: Triangle of number of permutations by barycenter.

Source: https://oeis.org/A062866
Credit: @Solfanbtc

The barycenter (signcenter) of a permutation is the sum of the signs of the differences between
final and initial positions of the objects; T(n,k) = number of permutations of n objects with
barycenter k (k ∈ ℤ, T(n,k) = T(n,-k)). Conjecture (Robert S. Maier, Jan 17 2025, in the
entry): e.g.f.
  Sum_{n>=0} Sum_k T(n,k) t^k z^n / n! = (1 - t^2) exp(z) / (exp(t z) - t^2 exp(z/t)).

Conventions.
* σ ∈ S_n = `Equiv.Perm (Fin n)`; barycenter(σ) = Σ_i sign(σ(i) - i) ∈ ℤ (`Int.sign`); the
  entry's example (1,3,2,5,7,6,4) has barycenter 1. P_n(t) = Σ_σ t^barycenter(σ) =
  Σ_k T(n,k) t^k, a Laurent polynomial (ℚ[T;T⁻¹], `LaurentPolynomial.T`).
* Writing F = Σ_n P_n z^n/n!, D = exp(tz) - t^2 exp(z/t), N = (1 - t^2) exp(z), the claim is
  F = N/D in ℚ(t)[[z]] (D has constant term 1 - t^2 ≠ 0, so it is invertible there), which is
  equivalent to F·D = N. Comparing coefficients of z^m/m! (binomial convolution of e.g.f.s):
  Σ_{n=0}^{m} C(m,n) P_n(t) (t^(m-n) - t^2 t^(-(m-n))) = 1 - t^2 for every m ≥ 0,
  an identity of Laurent polynomials, which is what is stated.
* python3 (exact, brute force over permutations): the identity holds for m = 0..8, and row 4
  is 1, 4, 14, 4, 1 (the data).
-/

namespace OMA.S_oeis_a062866

open LaurentPolynomial

/-- The barycenter of σ: Σ_i sign(σ(i) - i). -/
def barycenter {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℤ :=
  ∑ i : Fin n, Int.sign ((σ i : ℤ) - (i : ℤ))

/-- P_n(t) = Σ_σ t^barycenter(σ). -/
noncomputable def P (n : ℕ) : LaurentPolynomial ℚ :=
  ∑ σ : Equiv.Perm (Fin n), T (barycenter σ)

theorem main : ∀ m : ℕ,
    ∑ n ∈ Finset.range (m + 1),
        ((m.choose n : ℚ) • (P n * (T ((m : ℤ) - n) - T (2 - ((m : ℤ) - n)))))
      = 1 - T 2 := by
  sorry

end OMA.S_oeis_a062866
