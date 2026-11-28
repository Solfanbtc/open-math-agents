import Mathlib

/-!
# A102086: the row polynomials of the triangle with T(n,k) = [T^2](n-1,k)

Source: https://oeis.org/A102086
`T` (offset 0) is the lower triangular matrix with `T(n,n) = n + 1` and `T(n,k) = [T^2](n-1,k)`
for `n > k ≥ 0`, where `[T^2](n-1,k) = ∑_j T(n-1,j) T(j,k)` (only `k ≤ j ≤ n-1` contribute).
Rows: [1], [1,2], [3,4,3], [16,20,9,4], [127,156,63,16,5], ...

Conjecture (Mikhail Kurkov, Jul 03 2026): "n-th row polynomial is P(n+1, n) where
P(n, k) = P(n, k-1) + (k+1) * P(n-1, k) for 0 < k < n with P(n, n) = x^n, P(n, 0) = 1,
P(n, k) = 0 for k < 0 or k > n."
We state: for every `n ≥ 0`, `∑_{k=0}^{n} T(n,k) x^k = P(n+1, n)` in `ℕ[X]`.

Conventions. In `P`, the case `k = n` is applied before `k = 0`, so `P(0,0) = x^0 = 1`, which
agrees with both boundary conditions; `P(n, k)` for `k < 0` never arises with natural `k`
(the recursion only reaches `P(n, k-1)` with `k ≥ 1`).
Checked with python3: `T` reproduces all 47 listed terms, and the conjecture holds for
`n = 0..24`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a102086

open Polynomial

/-- The triangle A102086: `T n n = n + 1`, `T n k = [T^2](n-1,k)` for `k < n`, `0` for `k > n`. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if n + 1 < k then 0 else if k = n + 1 then n + 2 else
      ∑ j : Fin (n + 1), T n j * T j k
termination_by n => n
decreasing_by all_goals omega

/-- Kurkov's polynomials `P(n, k)`. -/
noncomputable def P : ℕ → ℕ → ℕ[X]
  | n, k =>
    if n < k then 0 else if k = n then X ^ n else if k = 0 then 1 else
      P n (k - 1) + C (k + 1) * P (n - 1) k
termination_by n k => (n, k)
decreasing_by all_goals (simp_wf; omega)

theorem main : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ k = P (n + 1) n := by
  sorry

end OMA.S_oeis_a102086
