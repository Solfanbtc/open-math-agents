import Mathlib

/-!
# A141222: Expansion of -1/(2*x) + (2*x-1)^2/(2*x*(1-4x)^(3/2)).

Source: https://oeis.org/A141222
Credit: @Solfanbtc

Claim (entry formula, conjectured by R. J. Mathar, 2012): for n ≥ 2 (so that a(n-2) is defined;
offset 0), (n+1)·a(n) + 2(-3n-1)·a(n-1) + 4(2n-3)·a(n-2) = 0.

Definition. a(n) is the coefficient of x^n in -1/(2x) + (2x-1)^2/(2x(1-4x)^(3/2)). Since
(1-4x)^(-3/2) = Σ_m (2m+1)·C(2m,m)·x^m, this coefficient is
a(n) = ((2n+3)C(2n+2,n+1) - 4(2n+1)C(2n,n) + 4(2n-1)C(2n-2,n-1))/2, with the last term absent
for n = 0 (the -1/(2x) cancels the x^(-1) term). That equals
a(n) = Σ_{k=0..n} C(2n,k)·C(n+1,2n-k), the entry formula used here. A python check: both
expressions agree for n < 300 and give all 26 listed terms 1, 5, 22, 95, ...; the recurrence
holds for 2 ≤ n < 300.
-/

namespace OMA.S_oeis_a141222

/-- A141222(n) = Σ_{k=0..n} C(2n,k)·C(n+1,2n-k). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (2 * n).choose k * (n + 1).choose (2 * n - k)

theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-3 * (n : ℤ) - 1) * a (n - 1) + 4 * (2 * (n : ℤ) - 3) * a (n - 2)
      = 0 := by
  sorry

end OMA.S_oeis_a141222
