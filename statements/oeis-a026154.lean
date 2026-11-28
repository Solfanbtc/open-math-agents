import Mathlib

/-!
# A026154: Mathar's recurrence for T(n, n-3) of the irregular triangle A026148

Source: https://oeis.org/A026154
Credit: @Solfanbtc

A026148: the irregular triangle `T(n, k)` with rows `[1]`, `[1, 1]`, `[1, 1, 2, 1, 1]`, and for
`n ≥ 3` row `n` has entries `k = 0, …, n + 2`: `T(n, 0) = 1`, `T(n, 1) = n - 1`,
`T(n, k) = T(n-1, k-2) + T(n-1, k-1) + T(n-1, k)` for `k = 2, …, n + 1`, and
`T(n, n+2) = T(n-1, n) + T(n-1, n+1)` (the entry's "T(n, k+2) = T(n-1, k) + T(n-1, k+1)", read
for the last entry `k = n`; entries outside a row are `0`). This reproduces the rows shown in
A026148: [1, 2, 4, 4, 4, 2], [1, 3, 7, 10, 12, 10, 6], [1, 4, 11, 20, 29, 32, 28, 16], ….
A026154 (offset 3): `a(n) = T(n, n-3)`; data 1, 3, 11, 35, 111, 343, …

Conjecture (R. J. Mathar, Jun 23 2013):
`(n+9) a(n) + (-7n-47) a(n-1) + (13n+51) a(n-2) + (5n+37) a(n-3) + 2(-13n-6) a(n-4)
 + 2(n-13) a(n-5) + 12(n-4) a(n-6) = 0`,
stated for `n ≥ 9` (so that every index is at least the offset 3).

Checked with python3: the rows above, the 14 listed terms, and the recurrence for `9 ≤ n < 110`.
-/

namespace OMA.S_oeis_a026154

/-- Row `n` of A026148. -/
def row : ℕ → List ℕ
  | 0 => [1]
  | 1 => [1, 1]
  | 2 => [1, 1, 2, 1, 1]
  | n + 3 =>
    let p := row (n + 2)
    let g := fun k => p.getD k 0
    [1, n + 2] ++ (List.range' 2 (n + 3)).map (fun k => g (k - 2) + g (k - 1) + g k) ++
      [g (n + 3) + g (n + 4)]

/-- A026154: `a(n) = T(n, n-3)`. -/
def a (n : ℕ) : ℕ := (row n).getD (n - 3) 0

/-- Mathar's recurrence for A026154, for `n ≥ 9`. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    ((n : ℤ) + 9) * a n + (-7 * (n : ℤ) - 47) * a (n - 1) + (13 * (n : ℤ) + 51) * a (n - 2)
      + (5 * (n : ℤ) + 37) * a (n - 3) + 2 * (-13 * (n : ℤ) - 6) * a (n - 4)
      + 2 * ((n : ℤ) - 13) * a (n - 5) + 12 * ((n : ℤ) - 4) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a026154
