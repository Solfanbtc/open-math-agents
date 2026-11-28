import Mathlib

/-!
# A026270: `T(n, n-1)`, `T` the array A026268

Source: https://oeis.org/A026270
Credit: @Solfanbtc

A026270 (offset 2): `1, 2, 6, 15, 39, 102, 270, 721, …`, "also `T(n, n-1)`, where `T` is the
array in A026268" (and A026268 records `T(n, n-1) = A026270(n)`, `n ≥ 2`, G. C. Greubel).

Definition used. The string description in the name is garbled: read literally
(`|s(2) - s(1)| = 1` excludes `s(2) = 1`, so the clause "if `s(2) = 1`" never applies, and
`a(2) = 0`) it gives `0, 2, 4, 11, 28, …`, and no small repair of it gives the data; the listed
g.f. is also shifted by one (its coefficient of `z^(n+1)` is `a(n)`). We therefore define the
sequence as `a(n) = T(n, n-1)` with `T` given by the recursive definition in the name of
A026268: `T(n, k) = 1` for `n < 3`; `T(3, 1) = T(3, 2) = T(3, 3) = 2`; `T(n, 0) = 1`;
`T(n, 1) = n - 1`; `T(n, n) = T(n-1, n-2) + T(n-1, n-1)`; otherwise
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)` (`0 ≤ k ≤ n`). This reproduces the 30 data terms of
A026268 and all 29 data terms of A026270.

Conjecture (R. J. Mathar, Jun 23 2013, OEIS formula):
`(n+3) a(n) + 3(-n-1) a(n-1) + (-n-1) a(n-2) + 3(n-5) a(n-3) = 0`.
Range: `n ≥ 5`, so that `a(n), …, a(n-3)` are all terms (offset 2). (Python: holds for
`5 ≤ n < 60`; it fails at `n = 4`, which involves `T(1, 0)`, outside the sequence.)
-/

namespace OMA.S_oeis_a026270

/-- The triangle A026268, by its recursive definition (`0` outside `0 ≤ k ≤ n`). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | 2, k => if k ≤ 2 then 1 else 0
  | 3, k => if k = 0 then 1 else if k ≤ 3 then 2 else 0
  | n + 4, k =>
    if k = 0 then 1
    else if k = 1 then n + 3
    else if k = n + 4 then T (n + 3) (n + 2) + T (n + 3) (n + 3)
    else if n + 4 < k then 0
    else T (n + 3) (k - 2) + T (n + 3) (k - 1) + T (n + 3) k

/-- A026270: `a(n) = T(n, n-1)`. -/
def a (n : ℕ) : ℕ := T n (n - 1)

/-- Mathar's conjectured recurrence for A026270. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 3) * a n + 3 * (-(n : ℤ) - 1) * a (n - 1) + (-(n : ℤ) - 1) * a (n - 2)
      + 3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026270
