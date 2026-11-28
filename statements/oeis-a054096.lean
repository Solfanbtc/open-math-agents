import Mathlib

/-!
# A054096: T(n,2), array T as in A054090.

Source: https://oeis.org/A054096
Credit: @Solfanbtc

A054090 is the triangle `T(n,0) = 1`, `T(n,1) = r(n-1)`,
`T(n,k) = T(n,k-1) - (-1)^k * r(n-k)` for `2 ≤ k ≤ n`, where `r(h) = Σ_{j=0..h} T(h,j)` is the
sum of row `h`. A054096 is `T(n,2)` for `n ≥ 2`: 1, 2, 6, 22, 98, 522, …

A006183 is `b(0) = 1`, `b(1) = 2`, `b(m) = (m+1) b(m-1) + (2-m) b(m-2)` (the entry's
Mathematica program; the entry's offset is 1, so A006183(m+1) = b(m)): 1, 2, 6, 22, 98, ….

Conjecture (Ralf Stephan, 2004): A054096 is A006183 shifted right, i.e. `T(n,2) = b(n-2)` for
every `n ≥ 2` (both lists start at their first term: A054096(2) = A006183(1) = 1).
Checked with python3 for `2 ≤ n < 60`.
-/

namespace OMA.S_oeis_a054096

/-- The triangle A054090, `T n k` for `k ≤ n` (values for `k > n` are not used; the case
`n = 0, k ≥ 1` is outside the triangle). The row sum `r(h)` is
`∑ j ∈ Finset.range (h + 1), T h j`. Checked with `#eval`: rows 0..9 equal the entry's
triangle. -/
def T : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 1 => ∑ j ∈ Finset.range (n + 1), T n j
  | n + 1, k + 2 =>
    T (n + 1) (k + 1) -
      (-1) ^ (k + 2) * ∑ j ∈ Finset.range (n + 1 - (k + 2) + 1), T (n + 1 - (k + 2)) j
termination_by n k => (n, k)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; omega)

/-- A006183, indexed from 0: `b 0 = 1`, `b 1 = 2`, `b m = (m+1) b(m-1) + (2-m) b(m-2)`. -/
def b : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | m + 2 => ((m : ℤ) + 3) * b (m + 1) - (m : ℤ) * b m

/-- The conjecture: `T(n,2) = A006183` shifted right. -/
theorem main : ∀ n : ℕ, 2 ≤ n → T n 2 = b (n - 2) := by
  sorry

end OMA.S_oeis_a054096
