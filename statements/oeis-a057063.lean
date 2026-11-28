import Mathlib

/-!
# A057063: limit of reverse-cyclic block permutations (prefix of length n fixed)

Source: https://oeis.org/A057063 (and https://oeis.org/A057033)
Credit: @Solfanbtc

For a sequence `s(1), s(2), ...`, `P(n)` leaves `s(1), ..., s(n)` fixed and reverse-cyclically
permutes every block of `n` consecutive terms thereafter; the entry's examples
(`PS(2) = 1,2,4,3,6,5,8`, `PS(3) = 1,2,4,6,5,3,7`, `PS(4) = 1,2,4,6,3,7,10`) show that a block
`(x₁, ..., xₙ)` becomes `(x₂, ..., xₙ, x₁)`. `PS(2) = P(2)(1, 2, 3, ...)`,
`PS(n+1) = P(n+1)(PS(n))`, and A057063 is the limit of `PS(n)`:
1, 2, 4, 6, 3, 10, 12, 7, ...
A057033 is the same construction where `P(n)` leaves only `s(1), ..., s(n-1)` fixed:
1, 3, 5, 2, 9, 11, 6, ...

Conjecture (Mikhail Kurkov, Mar 10 2022): `A057063(n) = A057033(n-1) + 1` for `n > 1`, with
`A057063(1) = 1`.

Encoding: sequences are functions `ℕ → ℕ` indexed from 1 (the value at 0 is unused).
`rotLeft f n s` fixes positions `≤ f` and rotates each block of `n` positions starting at `f + 1`
one step to the left. `PS k` is the sequence after the steps `P(2), ..., P(k)` (`PS 1` is
`1, 2, 3, ...`). Each position is changed only finitely often (step `k` fixes the first `k`,
resp. `k - 1`, positions), so the limit is the eventual value; we state the conjecture as
eventual equality at every position, which is exactly equality of the limits and needs no
separate limit definition.

Sanity check (python): the eventual values reproduce all 66 listed terms of A057063 and all 62 of
A057033, and the conjecture holds for `2 ≤ n ≤ 2000`; `#eval` in Lean gives the listed terms.
-/

namespace OMA.S_oeis_a057063

open Filter

/-- Fix positions `≤ f`; rotate each block of `n` consecutive positions starting at `f + 1` one
step to the left: `(x₁, ..., xₙ) ↦ (x₂, ..., xₙ, x₁)`. -/
def rotLeft (f n : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ f then s i
  else s (f + 1 + (i - (f + 1)) / n * n + ((i - (f + 1)) % n + 1) % n)

/-- `PS(k)` for A057063: step `m` fixes the first `m` terms. -/
def PS : ℕ → ℕ → ℕ
  | 0 => id
  | 1 => id
  | m + 2 => rotLeft (m + 2) (m + 2) (PS (m + 1))

/-- `PS(k)` for A057033: step `m` fixes the first `m - 1` terms. -/
def PS' : ℕ → ℕ → ℕ
  | 0 => id
  | 1 => id
  | m + 2 => rotLeft (m + 1) (m + 2) (PS' (m + 1))

/-- Kurkov's conjecture: `A057063(1) = 1` and `A057063(n) = A057033(n-1) + 1` for `n > 1`,
the limits being the eventual values of `PS` and `PS'`. -/
theorem main : (∀ᶠ k in atTop, PS k 1 = 1) ∧
    ∀ n : ℕ, 1 < n → ∀ᶠ k in atTop, PS k n = PS' k (n - 1) + 1 := by
  sorry

end OMA.S_oeis_a057063
