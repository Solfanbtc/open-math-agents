import Mathlib

/-!
# A108946: a(2n) = A001570(n), a(2n+1) = -A007654(n+1).

Source: https://oeis.org/A108946
Credit: @Solfanbtc

`a` (offset 0) has g.f. `(x^2+x+1)/((1-x)(1+x)(x^2+4x+1))` (OEIS %F), i.e. the recurrence with
signature `(-4, 0, 4, 1)` and initial terms `1, -3, 13, -48`, which reproduces the data.

Conjectures (C. Dement, OEIS %F), with `c(n) = a(n) - 4a(n+1) - a(n+2)` and
`d(n) = -a(n) - 4a(n+1) - a(n+2)`:
* I: `c(2n) = 24 · A076139(n)`, where A076139 = 0, 1, 15, 210, ... satisfies
  `t(n) = 14 t(n-1) - t(n-2) + 1`, `t(0) = 0`, `t(1) = 1`;
* II: `c(2n+1) = -A011943(n+1)`, where A011943 = 1, 7, 97, 1351, ... satisfies
  `s = 14 s' - s''`;
* III: `d(2n) = -2`;
* IV: `d(2n+1) = -1`.

Index fix for II: A011943 now has offset 1 (`A011943(1) = 1, A011943(2) = 7`), and with it II
fails at `n = 0`: `c(1) = -7` while `-A011943(1) = -1`. The values are
`c(1), c(3), c(5) = -7, -97, -1351`, i.e. `c(2n+1) = -A011943(n+2)` with the current offset,
or `-A011943(n+1)` with offset 0, presumably the convention when the comment was written.
We state II as `c(2n+1) = -s(n+1)`, where `s(0) = 1, s(1) = 7, s(2) = 97, ...` is A011943
read with offset 0. Checked in Python for `n < 25`; I, III and IV hold as written.
-/

namespace OMA.S_oeis_a108946

/-- A108946. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 13
  | 3 => -48
  | n + 4 => -4 * a (n + 3) + 4 * a (n + 1) + a n

/-- A076139: `0, 1, 15, 210, ...`. -/
def t : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 14 * t (n + 1) - t n + 1

/-- A011943 read with offset 0: `1, 7, 97, 1351, ...`. -/
def s : ℕ → ℤ
  | 0 => 1
  | 1 => 7
  | n + 2 => 14 * s (n + 1) - s n

def c (n : ℕ) : ℤ := a n - 4 * a (n + 1) - a (n + 2)

def d (n : ℕ) : ℤ := -a n - 4 * a (n + 1) - a (n + 2)

theorem main : ∀ n : ℕ, c (2 * n) = 24 * t n ∧ c (2 * n + 1) = -s (n + 1) ∧
    d (2 * n) = -2 ∧ d (2 * n + 1) = -1 := by
  sorry

end OMA.S_oeis_a108946
