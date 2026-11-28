import Mathlib

/-!
# A123483: the second-order Recamán sequence contains every natural number

Source: https://oeis.org/A123483 (with https://oeis.org/A005132)
A005132 (Recamán): `R(0) = 0`; for `n > 0`, `R(n) = R(n-1) - n` if nonnegative and not already in
the sequence, otherwise `R(n) = R(n-1) + n`: 0, 1, 3, 6, 2, 7, 13, ...
A123483: `a(0) = 0`; for `n > 0`, `a(n) = a(n-1) - R(n)` if that number is positive and not
already in the sequence, otherwise `a(n) = a(n-1) + R(n)`: 0, 1, 4, 10, 8, 15, 2, 22, ...
Conjecture (Franklin T. Adams-Watters): "this sequence contains every natural number."
(3, 6, 12 first appear at `n` = 4729925, 5808155, 2093396 (N. Hobson); some numbers below 100,
such as 7, had not appeared after `6·10^8` terms (S. R. Shannon, 2026).)

We state: every natural number `m` equals `a(n)` for some `n` (`0 = a(0)`).
Conventions. "Positive" is `a(n-1) > R(n)` (the difference `a(n-1) - R(n)` in `ℕ` is then the
true difference); for A005132, "nonnegative" is `R(n-1) ≥ n`. Prefix lists hold the terms so far.
Checked with `#eval`: `R(0..24)` and `a(0..25)` agree with the listed terms of both entries.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a123483

/-- `[R(0), ..., R(n)]` for Recamán's sequence A005132. -/
def recList : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let l := recList n
    let x := l.getLastD 0
    l ++ [if n + 1 ≤ x ∧ x - (n + 1) ∉ l then x - (n + 1) else x + (n + 1)]

/-- Recamán's sequence A005132. -/
def R (n : ℕ) : ℕ := (recList n).getLastD 0

/-- `[a(0), ..., a(n)]` for A123483. -/
def secList : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let l := secList n
    let x := l.getLastD 0
    l ++ [if R (n + 1) < x ∧ x - R (n + 1) ∉ l then x - R (n + 1) else x + R (n + 1)]

/-- A123483. -/
def a (n : ℕ) : ℕ := (secList n).getLastD 0

theorem main : ∀ m : ℕ, ∃ n : ℕ, a n = m := by
  sorry

end OMA.S_oeis_a123483
