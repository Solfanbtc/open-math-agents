import Mathlib

/-!
# A107026: Mathar's recurrences for the row sums of the inverse of the Riordan array (1/(1+x), x/(1+x)^4)

Source: https://oeis.org/A107026
The Riordan array `(1/(1+x), x/(1+x)^4)` has general term `M(n,k) = (-1)^(n-k) C(n+3k, 4k)`
(lower unitriangular). `a(n)` (offset 0) is the `n`-th row sum of its inverse:
1, 2, 10, 62, 426, 3112, ...
Two conjectures of R. J. Mathar (Feb 20 2015), stated together:
1. `189n(3n-1)(3n-2) a(n) + 72(-1034n^3+3098n^2-3754n+1655) a(n-1)
   + 384(2700n^3-12828n^2+20426n-10785) a(n-2) + 4096(-1066n^3+6666n^2-12950n+7365) a(n-3)
   - 65536(4n-15)(2n-7)(4n-13) a(n-4) = 0`, for `n ≥ 4`;
2. `3n(3n-1)(3n-2)(22n^2-62n+43) a(n) + 8(-1892n^5+8280n^4-13330n^3+9660n^2-3048n+315) a(n-1)
   + 128(4n-7)(2n-3)(4n-5)(22n^2-18n+3) a(n-2) = 0`, for `n ≥ 2`.
The ranges are those where all indices are `≥ 0` (offset 0). (Recurrence 2 would fail at `n = 1`
with `a(-1) = 0`: the left side is -84.)

Formalization. For each `N`, `M N` is the `N × N` truncation of the array; since the array is
lower unitriangular, the truncation of its inverse is the inverse of its truncation, so
`a n = ∑_k (M (n+1))⁻¹ n k`.
Checked with python3: the inverse's row sums reproduce the 21 listed terms and agree with the
entry's formula `3 C(4n,n) - 2 ∑_{k ≤ n} C(4n,k)`; both recurrences hold for all `n < 40` in
their ranges.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a107026

/-- The `N × N` truncation of the Riordan array `(1/(1+x), x/(1+x)^4)`. -/
def M (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun n k =>
  if (k : ℕ) ≤ n then
    (-1) ^ ((n : ℕ) - (k : ℕ)) * (((n : ℕ) + 3 * (k : ℕ)).choose (4 * (k : ℕ)) : ℚ) else 0

/-- A107026: the `n`-th row sum of the inverse of the Riordan array. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∑ k : Fin (n + 1), (M (n + 1))⁻¹ (Fin.last n) k

theorem main :
    (∀ n : ℕ, 4 ≤ n → let x : ℚ := n
      189 * x * (3 * x - 1) * (3 * x - 2) * a n
        + 72 * (-1034 * x ^ 3 + 3098 * x ^ 2 - 3754 * x + 1655) * a (n - 1)
        + 384 * (2700 * x ^ 3 - 12828 * x ^ 2 + 20426 * x - 10785) * a (n - 2)
        + 4096 * (-1066 * x ^ 3 + 6666 * x ^ 2 - 12950 * x + 7365) * a (n - 3)
        - 65536 * (4 * x - 15) * (2 * x - 7) * (4 * x - 13) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 2 ≤ n → let x : ℚ := n
      3 * x * (3 * x - 1) * (3 * x - 2) * (22 * x ^ 2 - 62 * x + 43) * a n
        + 8 * (-1892 * x ^ 5 + 8280 * x ^ 4 - 13330 * x ^ 3 + 9660 * x ^ 2 - 3048 * x + 315)
          * a (n - 1)
        + 128 * (4 * x - 7) * (2 * x - 3) * (4 * x - 5) * (22 * x ^ 2 - 18 * x + 3) * a (n - 2)
        = 0) := by
  sorry

end OMA.S_oeis_a107026
