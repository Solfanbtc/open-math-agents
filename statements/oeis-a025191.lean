import Mathlib

/-!
# A025191: a(n) = Sum_{k=0..n} T(n,k), where T is the array defined in A025177.

Source: https://oeis.org/A025191
Credit: @Solfanbtc

Conjectures (OEIS A025191, %F line): a(n) = A027914(n) - A027914(n-1)
= (A081673(n) - A081673(n-1))/2, for n >= 1 (offset 0, so n - 1 must be a valid index).

Definitions, from the entries:
* A025177: T(n, k) with g.f. (1 - yz)/(1 - z(1 + y + y^2)), i.e.
  T(n, k) = [y^k] (1 + y + y^2)^n - [y^(k-1)] (1 + y + y^2)^(n-1) for n, k >= 1, and
  T(n, k) = [y^k] (1 + y + y^2)^n when n = 0 or k = 0 (rows [1], [1, 0, 1], [1, 1, 2, 1, 1], ...).
* A027914(n) = T'(n, 0) + ... + T'(n, n), T' the trinomial array A027907, T'(n, k) = [y^k] (1 + y + y^2)^n.
* A081673: expansion (as an e.g.f.) of exp(3x) - exp(x) (1 - BesselI_0(2x)), with
  BesselI_0(2x) = Σ_j x^(2j) / (j!)^2; A081673(n) = n! [x^n] of that series.
Checked numerically: the definitions reproduce the listed terms (1, 1, 4, 11, 33, 97, ... for
A025191; 1, 3, 11, 33, 99, 293, ... for A081673) and both identities hold for 1 <= n < 40.
-/

namespace OMA.S_oeis_a025191

open Polynomial

/-- Trinomial coefficient `[y^k] (1 + y + y^2)^n` (A027907). -/
noncomputable def trin (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

/-- The array T of A025177. -/
noncomputable def T (n k : ℕ) : ℤ :=
  trin n k - if 1 ≤ n ∧ 1 ≤ k then trin (n - 1) (k - 1) else 0

/-- A025191(n) = Σ_{k=0..n} T(n, k). -/
noncomputable def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

/-- A027914(n) = Σ_{k=0..n} [y^k] (1 + y + y^2)^n. -/
noncomputable def A027914 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), trin n k

/-- The power series BesselI_0(2x) = Σ_j x^(2j) / (j!)^2. -/
noncomputable def besselI0Two : PowerSeries ℚ :=
  PowerSeries.mk fun m => if Even m then 1 / ((Nat.factorial (m / 2) : ℚ) ^ 2) else 0

/-- A081673(n) = n! [x^n] (exp(3x) - exp(x) (1 - BesselI_0(2x))). -/
noncomputable def A081673 (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) * PowerSeries.coeff n
    (PowerSeries.rescale (3 : ℚ) (PowerSeries.exp ℚ) - PowerSeries.exp ℚ * (1 - besselI0Two))

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = A027914 n - A027914 (n - 1) ∧
    (a n : ℚ) = (A081673 n - A081673 (n - 1)) / 2 := by
  sorry

end OMA.S_oeis_a025191
