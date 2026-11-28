import Mathlib

/-!
# A098301: Member r=16 of the family of Chebyshev sequences S_r(n) defined in A092184.

Source: https://oeis.org/A098301
Credit: @Solfanbtc

Sequences involved (with their OEIS offsets):
* A098301 (offset 0): `a(0) = 0`, `a(1) = 1`, `a(n) = 14 a(n-1) - a(n-2) + 2`
  (= `(T(n,7) - 1)/6`): 0, 1, 16, 225, 3136, ...
* A007655 (offset 1): `b(1) = 0`, `b(2) = 1`, `b(n) = 14 b(n-1) - b(n-2)`: 0, 1, 14, 195, 2716, ...
* A046184 (offset 1): the indices `m ≥ 1` of octagonal numbers `m (3m - 2)` that are squares, in
  increasing order: 1, 9, 121, 1681, ...
* A055793 (offset 1): the numbers `k` such that `k` and `⌊k/3⌋` are both squares, in increasing
  order: 0, 1, 4, 49, 676, ...

Conjecture (C. Dement, 2004): `4 A007655(n+1) + A046184(n) = A055793(n+2) + A098301(n+1)`.
Index fix: with A098301's present offset 0 this fails for every `n ≥ 1`: at `n = 1` the left
side is `4 + 1 = 5` and the right side `4 + 16 = 20`. The identity holds with `A098301(n)`
(5 = 4 + 1, 65 = 49 + 16, 901 = 676 + 225, ...; python3 for `1 ≤ n ≤ 8` with the listed data).
That matches the conjecture written when A098301 was indexed from 1. `main` states
`4 A007655(n+1) + A046184(n) = A055793(n+2) + A098301(n)` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a098301

/-- A098301 (offset 0). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 14 * a (n + 1) - a n + 2

/-- A007655 (offset 1; `b 0` is unused). -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => 14 * b (n + 2) - b (n + 1)

/-- A046184(n) (offset 1): indices of octagonal numbers that are squares. -/
noncomputable def c (n : ℕ) : ℕ := Nat.nth {m : ℕ | 1 ≤ m ∧ IsSquare (m * (3 * m - 2))} (n - 1)

/-- A055793(n) (offset 1): `k` with `k` and `⌊k/3⌋` both squares. -/
noncomputable def d (n : ℕ) : ℕ := Nat.nth {k : ℕ | IsSquare k ∧ IsSquare (k / 3)} (n - 1)

theorem main :
    ∀ n : ℕ, 1 ≤ n → 4 * b (n + 1) + (c n : ℤ) = (d (n + 2) : ℤ) + a n := by
  sorry

end OMA.S_oeis_a098301
