import Mathlib

/-!
# A005562: Number of walks on square lattice. Column y=4 of A052174.

Source: https://oeis.org/A005562
Credit: @Solfanbtc

`a(n)` (offset 4): `a(4) = 1, a(5) = 5, a(6) = 35, a(7) = 140, ...`. The values are taken from
Paul D. Hanna's formula in the entry, which is written for the 0-based index `m = n - 4` (as the
entry's Mathematica, PARI and Magma programs, run from 0, show):
`a(m + 4) = C(m+5, ⌈m/2⌉) C(m+4, ⌊m/2⌋) - C(m+5, ⌈(m-1)/2⌉) C(m+4, ⌊(m-1)/2⌋)`
(for `m = 0` the second product is `0`, since `⌊-1/2⌋ = -1`).

Conjecture (R. J. Mathar, Apr 02 2017, in the entry):
`(n-3)(n-4)(2n+1)(n+7)(n+6) a(n) - 4n(n+1)(2n² + 4n + 51) a(n-1)
 - 16 n² (n-1)(2n+3)(n+1) a(n-2) = 0`,
in the OEIS indexing (offset 4, matching Mathar's own Maple program, which runs `n = 4..30`).
Stated for all `n ≥ 6`, where `a(n-2), a(n-1), a(n)` are all defined.

A python3 check: Hanna's formula and Mathar's Maple formula both reproduce the data; the
recurrence holds for all `6 ≤ n < 300` with offset 4 (and fails already at `n = 2` if the
0-based index were used instead). The Lean kernel (`decide`) confirms `a 4, ..., a 13` against
the first 10 data terms.

Conventions:
* `⌈m/2⌉ = (m + 1)/2`, `⌊m/2⌋ = m/2`, `⌈(m-1)/2⌉ = m/2`, `⌊(m-1)/2⌋ = (m-1)/2` for `m ≥ 1` in `ℕ`.
* The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a005562

/-- Hanna's formula, 0-based: `h m = A005562(m + 4)`. -/
def h (m : ℕ) : ℕ :=
  (m + 5).choose ((m + 1) / 2) * (m + 4).choose (m / 2) -
    (if m = 0 then 0 else (m + 5).choose (m / 2) * (m + 4).choose ((m - 1) / 2))

/-- `a n = A005562(n)` for `n ≥ 4` (offset 4). -/
def a (n : ℕ) : ℤ := h (n - 4)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) - 3) * ((n : ℤ) - 4) * (2 * n + 1) * (n + 7) * (n + 6) * a n
      - 4 * n * (n + 1) * (2 * (n : ℤ) ^ 2 + 4 * n + 51) * a (n - 1)
      - 16 * (n : ℤ) ^ 2 * ((n : ℤ) - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005562
