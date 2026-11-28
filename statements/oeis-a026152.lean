import Mathlib

/-!
# A026152: a(n) = T(n,n-1), where T is the array in A026148.

Source: https://oeis.org/A026152
Credit: @Solfanbtc

A026148 is the irregular triangle with rows
`[1]`, `[1, 1]`, `[1, 1, 2, 1, 1]`, and for `n ≥ 3` row `n` has entries `T(n, 0..n+2)`:
`T(n, 0) = 1`, `T(n, 1) = n - 1`,
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)` for `2 ≤ k ≤ n + 1`, and
`T(n, n+2) = T(n-1, n) + T(n-1, n+1)` (the rule `T(n, k+2) = T(n-1, k) + T(n-1, k+1)` of the name,
for the last entry `k = n`). This reading reproduces all listed terms of A026148
(rows `1 2 4 4 4 2`, `1 3 7 10 12 10 6`, ...).

`a(n) = T(n, n-1)`, offset 2: 1, 4, 10, 29, 81, 230, ...

Conjecture (R. J. Mathar, Jun 23 2013), for `n ≥ 6` (so that `a(n-4)` is a term, offset 2):
`-(n+7)(31n-87) a(n) + (164n^2+313n-2115) a(n-1) + (-182n^2+229n+891) a(n-2)
 + (-164n^2+59n+519) a(n-3) + 3(71n-104)(n-3) a(n-4) = 0`.

Sanity check: python reproduces all listed terms of A026148 and all 27 listed terms of A026152
from this definition and confirms the recurrence for `6 ≤ n < 400`; `#eval` in Lean agrees.
-/

namespace OMA.S_oeis_a026152

/-- Row `n` of the triangle A026148, as a list `[T(n,0), T(n,1), ...]`. -/
def row : ℕ → List ℕ
  | 0 => [1]
  | 1 => [1, 1]
  | 2 => [1, 1, 2, 1, 1]
  | n + 3 =>
    let p := row (n + 2)
    let g : ℕ → ℕ := fun i => p.getD i 0
    [1, n + 2] ++ (List.range (n + 3)).map (fun j => g j + g (j + 1) + g (j + 2)) ++
      [g (n + 3) + g (n + 4)]

/-- The triangle A026148 (entries outside a row are `0`). -/
def T (n k : ℕ) : ℕ := (row n).getD k 0

/-- A026152: `a(n) = T(n, n-1)`. -/
def a (n : ℕ) : ℕ := T n (n - 1)

/-- Mathar's conjectured recurrence for A026152. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    let m : ℤ := n;
    -(m + 7) * (31 * m - 87) * a n + (164 * m ^ 2 + 313 * m - 2115) * a (n - 1)
      + (-182 * m ^ 2 + 229 * m + 891) * a (n - 2) + (-164 * m ^ 2 + 59 * m + 519) * a (n - 3)
      + 3 * (71 * m - 104) * (m - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026152
