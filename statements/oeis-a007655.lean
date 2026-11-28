import Mathlib

/-!
# A007655: Standard deviation of A007654

Source: https://oeis.org/A007655
Credit: @Solfanbtc

Conjectures (Creighton Dement, Nov 02 2004, OEIS formula):
1. `4 a(n+1) + A046184(n) = A055793(n+2) + A098301(n+1)`,
2. `4 a(n+1) + A098301(n+1) + A055793(n+2) = A046184(n+1)`,
3. `(4 a(n+1))^2 = A098301(2n+1)`.

The sequences, with their current OEIS offsets, each defined by a recurrence given in its entry
(each reproduces its listed data terms):
* `A007655` (offset 1): `0, 1, 14, 195, …`, `a(n) = 14 a(n-1) - a(n-2)`;
* `A046184` (offset 1): `1, 9, 121, 1681, …`, `a(n) = 14 a(n-1) - a(n-2) - 4`;
* `A055793` (offset 1): `0, 1, 4, 49, 676, …`, `a(n) = 14 a(n-1) - a(n-2) - 6` (from `a(4)` on);
* `A098301` (offset 0): `0, 1, 16, 225, …`, `a(n) = 14 a(n-1) - a(n-2) + 2`.

Offset fix (minimal, needed): with these offsets all three identities are false (e.g. (3) at
`n = 0` reads `0 = A098301(1) = 1`, and (1) at `n = 1` reads `4 + 1 = 4 + 16`). They all hold,
for every `n` in range, exactly when `A098301` is indexed from 1 (`A098301(1) = 0`,
`A098301(2) = 1`, …), i.e. when `A098301(m)` in the conjectures is read as the current
`A098301(m - 1)`; no other single reindexing of the four sequences makes all three hold
(checked by a search over shifts with Python). This is the reading stated below, through
`A098301'(m) := A098301(m - 1)`. (Identity (3) at index `2n + 1` thus says `(4 A007655(n+1))^2 =
A098301(2n)`, consistent with the OEIS formulas `a(n) = A001353(2n)/4`, `A098301(n) =
A001353(n)^2`.) Ranges: (1) for `n ≥ 1` (`A046184` starts at index 1), (2) and (3) for `n ≥ 0`.
Checked with Python for `n < 30`.
-/

namespace OMA.S_oeis_a007655

/-- `S n = A007655(n + 1)`. -/
def S : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 14 * S (n + 1) - S n

/-- `O n = A046184(n + 1)`. -/
def O : ℕ → ℤ
  | 0 => 1
  | 1 => 9
  | n + 2 => 14 * O (n + 1) - O n - 4

/-- `Q n = A055793(n + 1)`. -/
def Q : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | n + 3 => 14 * Q (n + 2) - Q (n + 1) - 6

/-- A098301 (offset 0). -/
def A098301 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 14 * A098301 (n + 1) - A098301 n + 2

/-- A007655 with its OEIS offset 1. -/
def A007655 (n : ℕ) : ℤ := S (n - 1)

/-- A046184 with its OEIS offset 1. -/
def A046184 (n : ℕ) : ℤ := O (n - 1)

/-- A055793 with its OEIS offset 1. -/
def A055793 (n : ℕ) : ℤ := Q (n - 1)

/-- A098301 indexed from 1, as in Dement's conjectures (see the module docstring). -/
def A098301' (m : ℕ) : ℤ := A098301 (m - 1)

/-- Dement's three identities for A007655. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      4 * A007655 (n + 1) + A046184 n = A055793 (n + 2) + A098301' (n + 1)) ∧
    (∀ n : ℕ, 4 * A007655 (n + 1) + A098301' (n + 1) + A055793 (n + 2) = A046184 (n + 1)) ∧
    (∀ n : ℕ, (4 * A007655 (n + 1)) ^ 2 = A098301' (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a007655
