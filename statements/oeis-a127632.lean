import Mathlib

/-!
# A127632: Expansion of c(x*c(x)), where c(x) is the g.f. for A000108.

Source: https://oeis.org/A127632
Credit: @Solfanbtc

Conjecture (R. J. Mathar, May 04 2018, in the entry):
3n(n-1)(4n-9)(n+1) a(n) - 8n(n-1)(20n^2-67n+48) a(n-1) + 8(4n-5)(n-1)(22n^2-94n+99) a(n-2)
  - 8(4n-11)(4n-5)(4n-9)(2n-5) a(n-3) = 0.

Conventions.
* c(x) = Σ_k Catalan(k) x^k (`catalan`). The composition c(x c(x)) = Σ_k Catalan(k) (x c(x))^k
  is a well-defined power series since (x c(x))^k has order k, so its n-th coefficient is the
  finite sum Σ_{k=0}^{n} Catalan(k) [x^n] (x c(x))^k, which is the definition used.
  python3: 1, 1, 3, 11, 44, 185, 804, 3579, 16229, 74690, ... (the data, offset 0).
* The recurrence involves a(n-3), so it is stated for n ≥ 3; checked for 3 ≤ n < 60.
* The entry's other remark, "Hankel transform appears to be A075845", is not included: A075845's
  defining matrix uses unspecified entries alpha(i), beta(j) in that entry.
-/

namespace OMA.S_oeis_a127632

/-- The Catalan generating function c(x). -/
def c : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

/-- A127632: coefficients of c(x c(x)). -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (catalan k : ℤ) * PowerSeries.coeff n ((PowerSeries.X * c) ^ k)

theorem main : ∀ n : ℕ, 3 ≤ n →
    let m : ℤ := n;
    3 * m * (m - 1) * (4 * m - 9) * (m + 1) * a n
      - 8 * m * (m - 1) * (20 * m ^ 2 - 67 * m + 48) * a (n - 1)
      + 8 * (4 * m - 5) * (m - 1) * (22 * m ^ 2 - 94 * m + 99) * a (n - 2)
      - 8 * (4 * m - 11) * (4 * m - 5) * (4 * m - 9) * (2 * m - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a127632
