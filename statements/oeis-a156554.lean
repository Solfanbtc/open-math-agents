import Mathlib

/-!
# A156554: The number of integer sequences of length d = 2n+1 such that the sum of the terms is 0 and the sum of the absolute values of the terms is d-1.

Source: https://oeis.org/A156554
Credit: @Solfanbtc

Conjectures (OEIS A156554, formula section, Peter Bala, Dec 19 2020 and Mar 17 2023):
(1) for any prime p >= 5, a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for all positive integers
    n and k;
(2) more generally, if r and s are positive integers, the same supercongruences hold for the
    sequence defined by [x^(r*n)] P(s*n, (1 + x)/(1 - x));
(3) even more generally, the same supercongruences hold for the sequence defined by
    [x^(r*n)] (1 + x)^(A*n) * (1 - x)^(B*n) * P(s*n, (1 + x)/(1 - x)), where A and B are
    integers.
Here P(m, y) is the m-th Legendre polynomial. All three are stated.

Conventions:
* a(n) is defined as in the name: the number of `f : Fin (2n+1) → ℤ` with
  `∑ f i = 0` and `∑ |f i| = 2n`. (Brute force in Python: 1, 6, 110 for n = 0, 1, 2.)
* All the series are formal power series over `ℚ`. Mathlib's `shiftedLegendre m` is
  `∑_k (-1)^k C(m,k) C(m+k,m) t^k = P(m, 1 - 2t)`, so P(m, y) is `shiftedLegendre m`
  evaluated at t = (1 - y)/2; for y = (1 + x)/(1 - x) this is t = -x/(1 - x), and
  `legendreAt m` is that power series. For negative exponents, `(1 ± x)^(e)` is the
  power of the inverse series (`zpowSeries`).
* "the same supercongruences" for a rational sequence b means
  b(n p^k) - b(n p^(k-1)) = p^(3k) * z for some integer z (the coefficients are integers,
  since 1 ± x are units of ℤ[[x]] and (1 - x)^m P(m, (1+x)/(1-x)) is an integer polynomial).
* Checked in Python with exact arithmetic: the coefficient [x^n] of `legendreAt (2n)` gives
  the data 1, 6, 110, 2562, 66222, 1815506, 51697802, and the congruences hold for
  p in {5, 7}, n in {1, 2}, k = 1 and (r, s, A, B) in {(1,2,0,0), (1,1,0,0), (2,3,0,0),
  (1,2,1,-2), (2,1,-1,3)}.
-/

namespace OMA.S_oeis_a156554

open PowerSeries

/-- A156554(n) by its definition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {f : Fin (2 * n + 1) → ℤ | ∑ i, f i = 0 ∧ ∑ i, |f i| = 2 * n}

/-- `P(m, (1 + x)/(1 - x))` as a power series in `x`. -/
noncomputable def legendreAt (m : ℕ) : PowerSeries ℚ :=
  Polynomial.aeval (-(X : PowerSeries ℚ) * (1 - X)⁻¹) (Polynomial.shiftedLegendre m)

/-- Integer powers of a power series (negative powers via the inverse). -/
noncomputable def zpowSeries (f : PowerSeries ℚ) (e : ℤ) : PowerSeries ℚ :=
  if 0 ≤ e then f ^ e.toNat else f⁻¹ ^ (-e).toNat

/-- `[x^(r n)] (1 + x)^(A n) (1 - x)^(B n) P(s n, (1 + x)/(1 - x))`. -/
noncomputable def b (r s : ℕ) (A B : ℤ) (n : ℕ) : ℚ :=
  coeff (r * n) (zpowSeries (1 + X) (A * n) * zpowSeries (1 - X) (B * n) * legendreAt (s * n))

/-- The supercongruences of Bala's conjectures for a rational sequence `c`. -/
def Supercongruent (c : ℕ → ℚ) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ∃ z : ℤ, c (n * p ^ k) - c (n * p ^ (k - 1)) = (p : ℚ) ^ (3 * k) * z

/-- Bala's three conjectures. -/
theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      (a (n * p ^ k) : ℤ) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]) ∧
    (∀ r s : ℕ, 1 ≤ r → 1 ≤ s → Supercongruent (b r s 0 0)) ∧
    (∀ r s : ℕ, 1 ≤ r → 1 ≤ s → ∀ A B : ℤ, Supercongruent (b r s A B)) := by
  sorry

end OMA.S_oeis_a156554
