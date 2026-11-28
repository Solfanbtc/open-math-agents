import Mathlib

/-!
# A006134: a(n) = Sum_{k=0..n} binomial(2*k,k)

Source: https://oeis.org/A006134
Credit: @Solfanbtc

Gus Wiseman (Apr 20 2023) lists among the formulas of the entry two conjectured identities:
* `a(n) = A013580(2n+1, n+1)` (conjectured), and
* `a(n) = A231147(2n+1, n+1)` (conjectured).
Both are stated, as a conjunction, for every `n ≥ 0`.

Conventions:
* `a n = ∑_{k=0}^{n} C(2k, k)` (offset 0).
* A013580 is the triangle `T(m, k)`, `0 ≤ k ≤ m`, built like Pascal's triangle except that `1` is
  added to the central element of each even-numbered row: `T(m, 0) = T(m, m) = 1` and, for
  `0 < k < m`, `T(m, k) = T(m-1, k-1) + T(m-1, k) + [m even ∧ k = m/2]`
  (rows `1; 1 1; 1 3 1; 1 4 4 1; 1 5 9 5 1; …`, as in the entry's data, indexed from 0 as the
  entry's offset says).
* Wiseman indexes A013580 from 1 in both row and column (his comment there: row `n = 5`, the
  subsets of `{1, …, 5}` by median `k = 1, …, 5`, is the row `1 5 9 5 1`, which is row 4 of the
  offset-0 triangle). So `A013580(2n+1, n+1)` in his notation is `T013580 (2n) n` here, the
  central entry of the even row `2n`. (Read with offset 0, `T(2n+1, n+1)` is `4, 14, 49, …`
  and the identity fails already at `n = 1`.)
* A231147 is the array of coefficients of the numerator polynomials of `p(m, x + 1/x)`, where
  `p(m, x) = (x^m - 1)/(x - 1) = 1 + x + ⋯ + x^{m-1}`; the numerator is
  `x^{m-1} p(m, x + 1/x) = ∑_{j<m} (x² + 1)^j x^{m-1-j}`, of degree `2m - 2`.
  Wiseman's column index `k` in `A231147(m, k)` runs over the half-step range `1, 3/2, …, m`
  (his reading: subsets of `{1, …, m}` by median `k`), so column `k` is the coefficient of
  `x^{2k-2}`; `A231147(2n+1, n+1)` is the central coefficient, of `x^{2n}`. For example row 5 is
  `1 1 5 4 9 4 5 1 1` and its central entry `9 = a(2)`. (Read with integer positions `n+1` the
  identity would already fail at `n = 2`, where that entry is `5`.) The rows of A231147 start
  at `m = 1` (offset 1), as for `numer231147 m` below.
* Both identities were checked in Python for `n ≤ 30`.
-/

namespace OMA.S_oeis_a006134

open Polynomial

/-- OEIS A006134. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * k) k

/-- The triangle A013580: Pascal's triangle with `1` added to the central element of each
even-numbered row. Entries outside `0 ≤ k ≤ m` are `0`. -/
def T013580 : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | m + 1, k =>
      if k = 0 ∨ k = m + 1 then 1
      else if m + 1 < k then 0
      else T013580 m (k - 1) + T013580 m k + (if (m + 1) % 2 = 0 ∧ 2 * k = m + 1 then 1 else 0)

/-- The numerator polynomial of `p(m, x + 1/x)`: `∑_{j<m} (x² + 1)^j x^{m-1-j}`. -/
noncomputable def numer231147 (m : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range m, (X ^ 2 + 1) ^ j * X ^ (m - 1 - j)

/-- Wiseman's conjectured identities `a(n) = A013580(2n+1, n+1)` (1-based indices: the central
entry of row `2n` from 0) and `a(n) = A231147(2n+1, n+1)` (central coefficient, of `x^{2n}`). -/
theorem main : ∀ n : ℕ,
    T013580 (2 * n) n = a n ∧
      (numer231147 (2 * n + 1)).coeff (2 * n) = (a n : ℤ) := by
  sorry

end OMA.S_oeis_a006134
