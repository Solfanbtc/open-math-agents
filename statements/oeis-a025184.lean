import Mathlib

/-!
# A025184: a(n) = T(2n,n), where T is the array defined in A025177.

Source: https://oeis.org/A025184
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Feb 25 2015, in the entry):
33n(3n-1)(3n-2) a(n) + 11(2047n^3-10725n^2+17192n-8520) a(n-1)
  + 9(-4397n^3-10169n^2+110500n-145368) a(n-2) - 54(2n-5)(5353n^2-33313n+53904) a(n-3)
  - 115668(2n-5)(2n-7)(n-4) a(n-4) = 0.

Conventions.
* A025177 has g.f. (1 - y z)/(1 - z(1 + y + y^2)) (entry formula): T(n,k) is the coefficient of
  y^k z^n, i.e. T(n,k) = [y^k] (1+y+y^2)^n - [y^(k-1)] (1+y+y^2)^(n-1) (second term absent for
  n = 0 or k = 0). This reproduces the rows 1; 1,0,1; 1,1,2,1,1; 1,2,4,4,4,2,1; ...
* a(n) = T(2n, n), offset 0. Checked with python3: all 21 listed terms (n = 0..20).
* The recurrence involves a(n-4), so it is stated for n ≥ 4; checked for 4 ≤ n < 60.
-/

namespace OMA.S_oeis_a025184

open Polynomial

/-- [y^k] (1 + y + y^2)^n. -/
noncomputable def tri (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

/-- A025177. -/
noncomputable def T (n k : ℕ) : ℤ := if n = 0 ∨ k = 0 then tri n k else tri n k - tri (n - 1) (k - 1)

/-- A025184. -/
noncomputable def a (n : ℕ) : ℤ := T (2 * n) n

theorem main : ∀ n : ℕ, 4 ≤ n →
    let m : ℤ := n;
    33 * m * (3 * m - 1) * (3 * m - 2) * a n
      + 11 * (2047 * m ^ 3 - 10725 * m ^ 2 + 17192 * m - 8520) * a (n - 1)
      + 9 * (-4397 * m ^ 3 - 10169 * m ^ 2 + 110500 * m - 145368) * a (n - 2)
      - 54 * (2 * m - 5) * (5353 * m ^ 2 - 33313 * m + 53904) * a (n - 3)
      - 115668 * (2 * m - 5) * (2 * m - 7) * (m - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025184
