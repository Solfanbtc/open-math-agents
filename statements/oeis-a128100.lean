import Mathlib

/-!
# A128100: Tilings of a 2 X n rectangle by k 2 X 2 tiles and n-2k 1 X 2 tiles.

Source: https://oeis.org/A128100
Credit: @Solfanbtc

Conjecture (Clark Kimberling, Oct 22 2014, in the entry): row n gives the coefficients of the
polynomial p(n,x), the numerator of f(n,x) = 1 + (x+1)/f(n-1,x), f(0,x) = 1; for n > 2,
p(n,x) is irreducible if and only if n is a (prime - 2).

Conventions.
* T(m,k) by Deléham's recurrence T(m,k) = T(m-1,k) + T(m-2,k) + T(m-2,k-1) with T(0,0) = 1,
  T(1,0) = 1 (and T = 0 outside 0 ≤ k ≤ m/2); it counts the tilings (rows 1; 1; 2,1; 3,2;
  5,5,1; 8,10,3; ...). R_m(x) = Σ_k T(m,k) x^k is the row-m polynomial.
* Indexing of p(n,x): from f(0) = 1, f(1) = x + 2, f(2) = (2x+3)/(x+2), ..., Kimberling's
  displayed list p = 1, 2 + x, 3 + 2x, 5 + 5x + x^2 is R_0 (or R_1), R_2, R_3, R_4: in general
  f(n) = R_(n+1)/R_n, so p(n,x) = R_(n+1)(x) for n ≥ 1. The statement is about p(n,x), n > 2.
  (Check: n = 3: R_4 = x^2 + 5x + 5 is irreducible and 3 + 2 = 5 is prime; n = 4:
  R_5 = 3x^2 + 10x + 8 = (3x + 4)(x + 2) and 6 is not prime.)
* Irreducibility is over ℚ (`Irreducible` in ℚ[X]).
-/

namespace OMA.S_oeis_a128100

/-- The triangle A128100 (0 outside the triangle). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 then 1 else 0
  | m + 2, k => T (m + 1) k + T m k + (if k = 0 then 0 else T m (k - 1))

open Polynomial

/-- Row polynomial R_m(x) = Σ_k T(m,k) x^k. -/
noncomputable def R (m : ℕ) : ℚ[X] := ∑ k ∈ Finset.range (m + 1), C (T m k : ℚ) * X ^ k

/-- Kimberling's p(n,x) = R_(n+1)(x). -/
noncomputable def p (n : ℕ) : ℚ[X] := R (n + 1)

theorem main : ∀ n : ℕ, 2 < n → (Irreducible (p n) ↔ (n + 2).Prime) := by
  sorry

end OMA.S_oeis_a128100
