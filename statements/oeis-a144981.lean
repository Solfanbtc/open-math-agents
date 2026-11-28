import Mathlib

/-!
# A144981: Decimal expansion of cos(Pi/8) = cos(22.5 degrees).

Source: https://oeis.org/A144981
Credit: @Solfanbtc

Conjecture (Simon Plouffe, Sep 09 2025, in the entry; also in A210065):
cos(Pi/8) = Sum_{k>=0} A210065(k) / exp(k*Pi).

Conventions.
* A210065 = coefficients of phi(q^2)/phi(q), with Ramanujan's phi(q) = Sum_{n∈ℤ} q^(n^2)
  = 1 + 2 Sum_{n≥1} q^(n^2) (A000122). As formal power series over ℤ: phi has constant term 1,
  hence is invertible, and A210065(k) = [q^k] phi(q^2) * phi(q)^(-1). Here
  phi(q) = Σ_m r(m) q^m with r(m) = #{n ∈ ℤ : n^2 = m} (r(0) = 1, r(j^2) = 2 for j ≥ 1),
  and phi(q^2) = Σ_m r(m) q^(2m). python3: 1, -2, 6, -12, 22, -40, 68, ... (the data).
* The series converges absolutely (|A210065(k)| grows like exp(π√k), entry asymptotic), so it
  is stated with `HasSum`. python3 (60 terms): 0.9238795325112867 on both sides.
-/

namespace OMA.S_oeis_a144981

/-- r(m) = number of integers n with n^2 = m. -/
def r (m : ℕ) : ℤ := if m = 0 then 1 else if IsSquare m then 2 else 0

/-- phi(q) = Σ_{n∈ℤ} q^(n^2). -/
def phi : PowerSeries ℤ := PowerSeries.mk r

/-- phi(q^2). -/
def phi2 : PowerSeries ℤ := PowerSeries.mk fun m => if m % 2 = 0 then r (m / 2) else 0

/-- A210065: coefficients of phi(q^2)/phi(q) (phi has constant term 1). -/
noncomputable def A210065 (k : ℕ) : ℤ := PowerSeries.coeff k (phi2 * phi.invOfUnit 1)

theorem main :
    HasSum (fun k : ℕ => (A210065 k : ℝ) / Real.exp (k * Real.pi)) (Real.cos (Real.pi / 8)) := by
  sorry

end OMA.S_oeis_a144981
