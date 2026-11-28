import Mathlib

/-!
# A111184: Triangle T(n,k), 0<=k<=n, read by rows, given by [0, 2, 1, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6, ...] DELTA [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, ...] where DELTA is the operator defined in A084938.

Source: https://oeis.org/A111184
Credit: @Solfanbtc

Conjectures (Mikhail Kurkov, Jul 15 2025), stated together as in the entry:
1. Sum_{k=1..n} T(n,k)*q^(k-1) = A111528(q,n) for n > 0, q >= 0.
2. Sum_{k=1..n} T(n,k)*(-1/q)^(k-1) = R(n,q)/q^(n-1) for n > 0, q > 0, where
   log(1 + x + q*x*[Sum_{k>=1} R(k,q)*x^k]) = Sum_{k>=1} R(k,q)/k*x^k.
3. The n-th row polynomial is x*v_n for n > 0, where we start with a vector v of fixed length m
   with all v_i = 1, and for i = 1..m-1, j = i+1..m apply A := v_i (at the beginning of each
   cycle for i) and also A := A + v_j, v_j := (j-i+x-1)*v_j + A.

Definitions.
* DELTA (A084938), as in the Mathematica program of the entry: with
  q_k = r_k x + s_k y, r = (0, 2, 1, 3, 2, 4, 3, ...) and s = (1, 0, 1, 0, ...) (indexed from 0),
  p(0, k) = 1, p(n, -1) = 0, p(n, k) = p(n, k-1) + q_k p(n-1, k+1), and T(n, k) is the
  coefficient of x^(n-k) y^k in p(n, 0). The homogeneous polynomial p(n, k) of degree n is
  stored as the list of its coefficients by powers of y. This reproduces the 45 data terms
  (`#eval`).
* A111528(q, n) (row q, column n of the square table): row q has g.f. R_q(x) with
  R_0(x) = Sum n! x^n and x R_{q+1}(x) = (1 + q x - 1/R_q(x))/(q+1), so the coefficient of x^k in
  R_{q+1} is the coefficient of x^(k+1) in (1 + q x - 1/R_q)/(q+1) (the constant term of that
  expression is 0 since R_q(0) = 1). Power series over ℚ.
* Conjecture 2: q is taken rational, q > 0 (both sides are polynomial in q and 1/q, so this is
  equivalent to the reading with integer q). The series Sum_{k>=1} R(k,q) x^k is `mk G` with
  `G 0 = 0`; with F = 1 + x + q x mk(G) (so F(0) = 1), the identity log F = Sum R(k,q)/k x^k is
  equivalent to its logarithmic derivative times x: x F' = F * mk(G). These relations determine
  `G` uniquely (coefficient recursion), and the statement is made for every `G` satisfying them.
* Conjecture 3: polynomials in ℤ[x]; `v` is indexed 1..m, and the claim is made for every m and
  every 1 ≤ n ≤ m (v_n does not depend on m ≥ n).
All three were checked with python3 (conjecture 1 for n ≤ 9, q ≤ 7 where the series were
computed exactly; conjecture 2 for n ≤ 9 and q ∈ {1, 2, 3, 1/2, 5/3}; conjecture 3 for m = 10).
-/

namespace OMA.S_oeis_a111184

open Polynomial

/-- r = (0, 2, 1, 3, 2, 4, 3, 5, ...), indexed from 0. -/
def r (i : ℕ) : ℕ := if i = 0 then 0 else if i % 2 = 1 then i / 2 + 2 else i / 2

/-- s = (1, 0, 1, 0, ...), indexed from 0. -/
def s (i : ℕ) : ℕ := if i % 2 = 0 then 1 else 0

/-- Multiply a homogeneous polynomial (coefficients by powers of y) by q_i = r_i x + s_i y. -/
def mulq (i : ℕ) (c : List ℕ) : List ℕ :=
  (List.range (c.length + 1)).map fun j =>
    r i * c.getD j 0 + s i * (if j = 0 then 0 else c.getD (j - 1) 0)

/-- Coefficientwise sum of two lists. -/
def addL (a b : List ℕ) : List ℕ :=
  (List.range (max a.length b.length)).map fun j => a.getD j 0 + b.getD j 0

/-- p(n, k) of the DELTA construction = Sum_{i=0..k} q_i p(n-1, i+1). -/
def p : ℕ → ℕ → List ℕ
  | 0, _ => [1]
  | n + 1, k => (List.range (k + 1)).foldl (fun acc i => addL acc (mulq i (p n (i + 1)))) []

/-- A111184: T(n, k). -/
def T (n k : ℕ) : ℕ := (p n 0).getD k 0

/-- Row q of A111528 as a power series over ℚ. -/
noncomputable def R : ℕ → PowerSeries ℚ
  | 0 => PowerSeries.mk fun k => (k.factorial : ℚ)
  | q + 1 => PowerSeries.mk fun k =>
      PowerSeries.coeff (k + 1) (1 + (q : ℚ) • PowerSeries.X - (R q)⁻¹) / ((q : ℚ) + 1)

/-- A111528(q, n). -/
noncomputable def A111528 (q n : ℕ) : ℚ := PowerSeries.coeff n (R q)

/-- One inner cycle (fixed `i`) of the algorithm of conjecture 3, over the indices `js`. -/
noncomputable def inner (i : ℕ) : List ℕ → (ℕ → ℤ[X]) → ℤ[X] → (ℕ → ℤ[X])
  | [], v, _ => v
  | j :: js, v, A =>
    let A' := A + v j
    inner i js (Function.update v j ((C ((j : ℤ) - i - 1) + X) * v j + A')) A'

/-- The outer loop over `i ∈ is`. -/
noncomputable def outer (m : ℕ) : List ℕ → (ℕ → ℤ[X]) → (ℕ → ℤ[X])
  | [], v => v
  | i :: is, v => outer m is (inner i (List.range' (i + 1) (m - i)) v (v i))

/-- The vector `v` (indexed 1..m) at the end of the algorithm. -/
noncomputable def algo (m : ℕ) : ℕ → ℤ[X] := outer m (List.range' 1 (m - 1)) fun _ => 1

/-- The n-th row polynomial of A111184. -/
noncomputable def rowPoly (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n + 1), C (T n k : ℤ) * X ^ k

theorem main :
    (∀ n q : ℕ, 0 < n →
      (∑ k ∈ Finset.Icc 1 n, (T n k : ℚ) * (q : ℚ) ^ (k - 1)) = A111528 q n) ∧
    (∀ q : ℚ, 0 < q → ∀ G : ℕ → ℚ, G 0 = 0 →
      (PowerSeries.X * PowerSeries.derivative ℚ
          (1 + PowerSeries.X + PowerSeries.C q * PowerSeries.X * PowerSeries.mk G) =
        (1 + PowerSeries.X + PowerSeries.C q * PowerSeries.X * PowerSeries.mk G) *
          PowerSeries.mk G) →
      ∀ n : ℕ, 0 < n →
        (∑ k ∈ Finset.Icc 1 n, (T n k : ℚ) * (-1 / q) ^ (k - 1)) = G n / q ^ (n - 1)) ∧
    (∀ m n : ℕ, 1 ≤ n → n ≤ m → X * algo m n = rowPoly n) := by
  sorry

end OMA.S_oeis_a111184
