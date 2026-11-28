import Mathlib

/-!
# A025757: 4th-order Vatalan numbers (generalization of Catalan numbers).

Source: https://oeis.org/A025757
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jul 28 2014, in the entry):
5n(n-1)(n-2) a(n) - (239n-600)(n-1)(n-2) a(n-1) + 24(n-2)(158n^2-953n+1445) a(n-2)
  + 16(-1232n^3+13056n^2-45949n+53730) a(n-3) - 128(4n-15)(2n-7)(4n-13) a(n-4) = 0.

Conventions.
* Definition by the entry's g.f. 4 / (3 + (1-16x)^(1/4)), offset 0. The power series
  (1-16x)^(1/4) is Σ_k C(1/4, k) (-16)^k x^k (generalized binomial coefficient `Ring.choose`
  over ℚ); 3 + (1-16x)^(1/4) has constant term 4, so it is invertible in ℚ⟦x⟧. Checked with
  python3: the coefficients are 1, 1, 7, 69, 783, ..., all 23 listed terms.
* The recurrence involves a(n-4), so it is stated for n ≥ 4 (all indices ≥ 0); checked for
  4 ≤ n < 60.
-/

namespace OMA.S_oeis_a025757

/-- The power series (1 - 16x)^(1/4). -/
noncomputable def F : PowerSeries ℚ :=
  PowerSeries.mk fun k => Ring.choose (1 / 4 : ℚ) k * (-16 : ℚ) ^ k

/-- A025757: coefficients of 4 / (3 + (1-16x)^(1/4)). -/
noncomputable def a (n : ℕ) : ℚ :=
  PowerSeries.coeff n (PowerSeries.C (4 : ℚ) * (PowerSeries.C (3 : ℚ) + F)⁻¹)

theorem main : ∀ n : ℕ, 4 ≤ n →
    let m : ℚ := n;
    5 * m * (m - 1) * (m - 2) * a n - (239 * m - 600) * (m - 1) * (m - 2) * a (n - 1)
      + 24 * (m - 2) * (158 * m ^ 2 - 953 * m + 1445) * a (n - 2)
      + 16 * (-1232 * m ^ 3 + 13056 * m ^ 2 - 45949 * m + 53730) * a (n - 3)
      - 128 * (4 * m - 15) * (2 * m - 7) * (4 * m - 13) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025757
