import Mathlib

/-!
# A112486: Coefficient triangle for polynomials used for e.g.f.s for unsigned Stirling1 diagonals.

Source: https://oeis.org/A112486
Credit: @Solfanbtc

Conjecture (Mikhail Kurkov, Apr 21 2025): the row polynomials are
  R(n,x) = Sum_{i=0..n} Sum_{j=0..i} Sum_{k=0..j}
             (n+i)! * Stirling2(n+j-k, j-k) * x^k * (x+1)^(j-k) * (-1)^(n+j+k)
             / ((n+j-k)! * (i-j)! * k!).

Definitions.
* The triangle (formula section and Maple program): a(0,0) = 1, a(n,k) = 0 if k < 0 or k > n,
  and a(n,k) = (n+k) a(n-1,k) + (n+k-1) a(n-1,k-1) for n ≥ 1. It reproduces the data
  1; 1, 1; 2, 5, 3; 6, 26, 35, 15; ... (`#eval`). Row polynomial R(n,x) = Sum_k a(n,k) x^k,
  in `ℚ[X]` (the right-hand side has rational coefficients termwise).
* Statement: R(n, x) equals Kurkov's triple sum for every n ≥ 0 (as polynomials).
  python3 (exact rationals): holds for n ≤ 11.

The entry contains one other hedged remark, by Tom Copeland (Oct 05 2011): "Apparently,
P(n,t) = (-1)^(n+1) PW[n,-(1+t)] where PW are the Ward polynomials A134991", for the listed
signed polynomials P(n,t). Read literally it already fails at n = 2: P(2,t) = -(1+t) while
PW[2,s] = s gives (-1)^3 PW[2,-(1+t)] = 1+t (and similarly at n = 4); without the sign factor
it follows from the two e.g.f.s given in the entries (B(x) = x + (t+1)(e^x - x - 1) is the
Ward inverse series at -(1+t)). It is therefore not part of this statement.
-/

namespace OMA.S_oeis_a112486

open Polynomial

/-- A112486: a(n, k), defined through the row lists. `row n = [a(n,0), ..., a(n,n)]`. -/
def row : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
    let r := row n
    (List.range (n + 2)).map fun k =>
      (n + 1 + k) * r.getD k 0 + (if k = 0 then 0 else (n + k) * r.getD (k - 1) 0)

/-- a(n, k). -/
def T (n k : ℕ) : ℕ := (row n).getD k 0

/-- Row polynomial R(n, x). -/
noncomputable def R (n : ℕ) : ℚ[X] := ∑ k ∈ Finset.range (n + 1), C (T n k : ℚ) * X ^ k

/-- Kurkov's triple sum. -/
noncomputable def K (n : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), ∑ k ∈ Finset.range (j + 1),
    C (((n + i).factorial : ℚ) * (Nat.stirlingSecond (n + j - k) (j - k) : ℚ) *
        (-1) ^ (n + j + k) /
        (((n + j - k).factorial : ℚ) * ((i - j).factorial : ℚ) * (k.factorial : ℚ))) *
      X ^ k * (X + 1) ^ (j - k)

theorem main : ∀ n : ℕ, R n = K n := by
  sorry

end OMA.S_oeis_a112486
