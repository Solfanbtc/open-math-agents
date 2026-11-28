import Mathlib

/-!
# A112283: Consider the array T(n, m) where the n-th row is the sequence of integer coefficients of A(x), where 1<=a(n)<=n, such that A(x)^(1/n) consists entirely of integer coefficients and where m is the (m+1)-th coefficient. This sequence is the first occurrence of 1 after the first column.

Source: https://oeis.org/A112283
Credit: @Solfanbtc

Conjecture (entry formula section): "a(n)=n if n is 1, a prime or the square of the odd primes."
This is read as the implication stated (not an iff: a(27) = 27 although 27 is neither, and
a(4) = 8 shows why the square of the even prime is excluded).

Definitions.
* Row n of A109626 (the array T): T(n,0) = 1 and, greedily as in the Mathematica program,
  T(n,l) for l ≥ 1 is the least k with 1 ≤ k ≤ n such that the series with coefficients
  T(n,0), ..., T(n,l-1), k has an n-th root with integer coefficients up to degree l, i.e. there
  is an integer polynomial B with B(0) = 1 whose n-th power agrees with it in degrees ≤ l.
  (Adding n x^l changes the l-th coefficient of the root by exactly 1, so exactly one k in
  [1, n] works.)
* a(n) (offset 1) is the least l > 0 with T(n,l) = 1.
* python3 (exact integer recursion for the n-th root): reproduces the data for n ≤ 30, and
  a(n) = n for every prime n < 300 and for n = p^2 with p = 3, 5, 7, 11, 13, 17.
-/

namespace OMA.S_oeis_a112283

open Polynomial

/-- The coefficient list `c` (degrees `0..c.length-1`) agrees with the `n`-th power of an
integer polynomial with constant term 1. -/
def HasIntRoot (n : ℕ) (c : List ℤ) : Prop :=
  ∃ B : ℤ[X], B.coeff 0 = 1 ∧ ∀ j < c.length, (B ^ n).coeff j = c.getD j 0

/-- `row n l = [T(n,0), ..., T(n,l)]`. -/
noncomputable def row (n : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | l + 1 =>
    let r := row n l
    r ++ [((sInf {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ HasIntRoot n (r ++ [(k : ℤ)])} : ℕ) : ℤ)]

/-- T(n, l). -/
noncomputable def T (n l : ℕ) : ℤ := (row n l).getD l 0

/-- A112283(n). -/
noncomputable def a (n : ℕ) : ℕ := sInf {l : ℕ | 0 < l ∧ T n l = 1}

theorem main :
    ∀ n : ℕ, 1 ≤ n → (n = 1 ∨ n.Prime ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ n = p ^ 2) → a n = n := by
  sorry

end OMA.S_oeis_a112283
