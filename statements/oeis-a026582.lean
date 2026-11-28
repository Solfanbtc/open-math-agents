import Mathlib

/-!
# A026582: a(n) = Sum{T(i,j)}, 0<=j<=i, 0<=i<=n, T given by A026568.

Source: https://oeis.org/A026582
Credit: @Solfanbtc

A026568 is the irregular triangle `T(i, j)`, `0 ≤ j ≤ 2i`. We use its combinatorial description
(comment in A026568): `T(n, k)` is the number of strings `s(0), ..., s(n)` of integers with
`s(0) = 0`, `s(n) = n - k`, and for `1 ≤ i ≤ n`: `|s(i) - s(i-1)| ≤ 1` if `s(i-1)` is even,
`|s(i) - s(i-1)| = 1` if `s(i-1)` is odd. (The recursive definition in the name of A026568 has the
typo `2 ≤ j ≤ i - 2` for `2 ≤ j ≤ 2i - 2`; the walk description is unambiguous, and it reproduces
all listed terms of A026568.) `walks n s` counts such strings of length `n` ending at `s`.

`a(n) = ∑_{i=0..n} ∑_{j=0..i} T(i, j)`: 1, 3, 8, 20, 50, 125, ... (offset 0).

Conjecture (R. J. Mathar, Jun 23 2013), for `n ≥ 6` (so that all indices are `≥ 0`):
`n a(n) + 2(-2n+1) a(n-1) + 2(-n+3) a(n-2) + 20(n-2) a(n-3) + (-7n+6) a(n-4)
 + 2(-12n+41) a(n-5) + 8(2n-7) a(n-6) = 0`.

Sanity check: python gives all listed terms of A026568 and all 28 listed terms of A026582 from
this definition, and the recurrence for `6 ≤ n < 300`; `#eval` in Lean gives the first six rows of A026568 and the first 13 terms of `a`.
-/

namespace OMA.S_oeis_a026582

/-- Number of strings `s(0) = 0, ..., s(n) = s` with steps in `{-1, 0, 1}` from an even value and
in `{-1, 1}` from an odd value. -/
def walks : ℕ → ℤ → ℕ
  | 0, s => if s = 0 then 1 else 0
  | n + 1, s => walks n (s - 1) + walks n (s + 1) + (if Even s then walks n s else 0)

/-- The triangle A026568: `T(n, k)` = number of such strings ending at `n - k`. -/
def T (n k : ℕ) : ℕ := walks n ((n : ℤ) - k)

/-- A026582. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), T i j

/-- Mathar's conjectured recurrence for A026582. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    let m : ℤ := n
    m * a n + 2 * (-2 * m + 1) * a (n - 1) + 2 * (-m + 3) * a (n - 2) + 20 * (m - 2) * a (n - 3)
      + (-7 * m + 6) * a (n - 4) + 2 * (-12 * m + 41) * a (n - 5) + 8 * (2 * m - 7) * a (n - 6)
      = 0 := by
  sorry

end OMA.S_oeis_a026582
