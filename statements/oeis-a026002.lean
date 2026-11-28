import Mathlib

/-!
# A026002: a(n) = T(n,n+2), where T = Delannoy triangle (A008288).

Source: https://oeis.org/A026002
Credit: @Solfanbtc

Conjecture (J. M. Bergot, Apr 24 2013): define an infinite array to have
m(n,1) = m(1,n) = n*(n-1)+1 in the first row and column, and
m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j); then m(n,n) = a(n).

Conventions.
* `delannoy m n = ∑_{k} C(m,k) C(n,k) 2^k` is the Delannoy number D(m,n), the square-array
  form of A008288 (it satisfies D(0,n) = D(m,0) = 1 and
  D(m+1,n+1) = D(m,n+1) + D(m,n) + D(m+1,n)).
* The sequence has offset 1 and is the (+-)2-diagonal of that square array:
  a(n) = D(n-1, n+1) for n ≥ 1, giving 1, 7, 41, 231, 1289, ... as in the OEIS data
  (equivalently a(n) = Sum_{k=0..n-1} C(n-1,k) C(n+1,k) 2^k, Barry's formula shifted to offset 1).
* The array `m` is indexed from 1 as in the source; `arr i j` stores m(i+1, j+1).
  The first row and column are m(1,n) = m(n,1) = n(n-1)+1 (consistent at m(1,1) = 1), and the
  recurrence applies for i, j ≥ 2.
* The claim is for all n ≥ 1 (the indices of both the array and the sequence start at 1).
  Checked numerically for n ≤ 30.
-/

namespace OMA.S_oeis_a026002

/-- Delannoy number D(m,n) (A008288 as a square array). -/
def delannoy (m n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (min m n + 1), m.choose k * n.choose k * 2 ^ k

/-- A026002, offset 1: a(n) = D(n-1, n+1). -/
def a (n : ℕ) : ℕ := delannoy (n - 1) (n + 1)

/-- 0-based storage of Bergot's array: `arr i j = m(i+1, j+1)`. -/
def arr : ℕ → ℕ → ℕ
  | 0, j => (j + 1) * j + 1
  | i + 1, 0 => (i + 2) * (i + 1) + 1
  | i + 1, j + 1 => arr (i + 1) j + arr i j + arr i (j + 1)

/-- Bergot's array, 1-indexed as in the source. -/
def m (i j : ℕ) : ℕ := arr (i - 1) (j - 1)

theorem main : ∀ n : ℕ, 1 ≤ n → m n n = a n := by
  sorry

end OMA.S_oeis_a026002
