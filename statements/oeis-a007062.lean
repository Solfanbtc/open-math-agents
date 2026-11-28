import Mathlib

/-!
# A007062: Let P(n) of a sequence s(1),s(2),s(3),... be obtained by leaving s(1),...,s(n) fixed and reversing every n consecutive terms thereafter; apply P(2) to 1,2,3,... to get PS(2), then apply P(3) to PS(2) to get PS(3), then apply P(4) to PS(3), etc. This sequence is the limit of PS(n).

Source: https://oeis.org/A007062
Credit: @Solfanbtc

A007062 is the limit of `PS(n)`, where `PS(1) = 1, 2, 3, ...` and `PS(n) = P(n)(PS(n-1))`, `P(n)`
leaving `s(1), ..., s(n)` fixed and reversing every block of `n` consecutive terms after them:
`1, 2, 4, 5, 7, 12, 14, ...`. A057030 is the same construction with `P'(n)` leaving only
`s(1), ..., s(n-1)` fixed: `1, 3, 4, 6, 11, 13, ...`.

Conjecture (Mikhail Kurkov, Feb 24 2023, in the entry): `a(n) = A057030(n-1) + 1` for `n > 1`,
with `a(1) = 1`.

The limits are expressed directly: for each position `i`, `PS(m)(i)` (resp. `PS'(m)(i)`) is
eventually constant in `m` (`P(m)` fixes positions `≤ m`), and the conjecture says that
eventually (for all large `m`) `PS(m)(n) = PS'(m)(n-1) + 1` for `n > 1`, and `PS(m)(1) = 1`.

A python3 check with exactly these definitions reproduces 51 terms of A007062 and 40 terms of
A057030, and the relation holds for `2 ≤ n ≤ 40`. The Lean kernel (`decide`) confirms that
`PS 11` and `PS' 11` start with the first 10 data terms of A007062 and A057030.

Conventions:
* Sequences are functions `ℕ → ℕ` indexed from 1 (the value at 0 is never used).
* `P n s i`: for `i ≤ n`, `s i`; for `i = n + 1 + q n + r` (`0 ≤ r < n`), `s (n + 1 + q n + (n - 1 - r))`.
  `P' n s i`: for `i ≤ n - 1`, `s i`; for `i = n + q n + r`, `s (n + q n + (n - 1 - r))`.
* `PS 0 = PS 1 = id`, `PS (n + 1) = P (n + 1) (PS n)`; likewise `PS'`.
-/

namespace OMA.S_oeis_a007062

open Filter

/-- `P(n)`: fix `s(1..n)`, reverse each following block of `n` terms. -/
def P (n : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ n then s i else
    s (n + 1 + (i - n - 1) / n * n + (n - 1 - (i - n - 1) % n))

/-- `P'(n)`: fix `s(1..n-1)`, reverse each following block of `n` terms. -/
def P' (n : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ n - 1 then s i else
    s (n + (i - n) / n * n + (n - 1 - (i - n) % n))

/-- `PS(n)` for A007062. -/
def PS : ℕ → ℕ → ℕ
  | 0 => id
  | 1 => id
  | n + 2 => P (n + 2) (PS (n + 1))

/-- `PS'(n)` for A057030. -/
def PS' : ℕ → ℕ → ℕ
  | 0 => id
  | 1 => id
  | n + 2 => P' (n + 2) (PS' (n + 1))

/-- Kurkov's conjecture, with the limits taken along `m → ∞`: `a(1) = 1` and
`a(n) = A057030(n - 1) + 1` for `n > 1`. -/
theorem main : (∀ᶠ m in atTop, PS m 1 = 1) ∧
    ∀ n : ℕ, 1 < n → ∀ᶠ m in atTop, PS m n = PS' m (n - 1) + 1 := by
  sorry

end OMA.S_oeis_a007062
