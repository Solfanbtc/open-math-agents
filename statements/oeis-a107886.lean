import Mathlib

/-!
# A107886: Column 1 of triangle A107884.

Source: https://oeis.org/A107886
Credit: @Solfanbtc

Conjecture (Benedict W. J. Irwin, Nov 26 2016): a(n) can be expressed with a series of nested
sums,
  a(2) = Sum_{i=1..3} i+1,
  a(3) = Sum_{i=1..3} Sum_{j=1..i+1} j+2,
  a(4) = Sum_{i=1..3} Sum_{j=1..i+1} Sum_{k=1..j+2} k+3,
  a(5) = Sum_{i=1..3} Sum_{j=1..i+1} Sum_{k=1..j+2} Sum_{l=1..k+3} l+4.

Definitions.
* a(n) (offset 0) is defined by the g.f. relation of the entry (the column-1 case of the g.f.
  of A107884): 1 = Sum_{k>=0} a(k) x^k (1-x)^(3 + k(k+1)/2), i.e. (as in the PARI program)
  a(n) = [n = 0] - Sum_{k<n} a(k) (-1)^(n-k) C(3 + k(k+1)/2, n-k). This reproduces all 19 data
  terms (python3, `#eval`).
* The nested sums. The pattern of the examples is: n - 1 nested sums, the t-th over
  `1 ≤ i_t ≤ i_(t-1) + (t-1)` with `i_0 = 3`, of the summand `i_(n-1) + (n-1)`. Writing the
  summand as one more sum of 1's, this is `N n 3 0` where `N 0 k j = 1` and
  `N (n+1) k j = Sum_{i=1..k+j} N n i (j+1)` (the recursion of Michael Somos's Mathematica
  program in the entry). `N 2 3 0 = Sum_{i=1..3} (i+1)`, etc.
* Statement: a(n) = N n 3 0 for every n ≥ 2 (the range of the examples; it also holds for
  n = 0, 1). python3: holds for n ≤ 11.
-/

namespace OMA.S_oeis_a107886

/-- `terms n = [a(0), ..., a(n-1)]`. -/
def terms : ℕ → List ℤ
  | 0 => []
  | n + 1 =>
    let L := terms n
    L ++ [(if n = 0 then 1 else 0) - ∑ k ∈ Finset.range n,
      L.getD k 0 * (-1) ^ (n - k) * ((3 + k * (k + 1) / 2).choose (n - k) : ℤ)]

/-- A107886(n). -/
def a (n : ℕ) : ℤ := (terms (n + 1)).getD n 0

/-- The nested sums. -/
def N : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, k, j => ∑ i ∈ Finset.Icc 1 (k + j), N n i (j + 1)

theorem main : ∀ n : ℕ, 2 ≤ n → (N n 3 0 : ℤ) = a n := by
  sorry

end OMA.S_oeis_a107886
