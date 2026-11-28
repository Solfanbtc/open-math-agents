import Mathlib

/-!
# A133058: a(0) = a(1) = 1; for n > 1, a(n) = a(n-1) + n + 1 if a(n-1) and n are coprime, otherwise a(n) = a(n-1)/gcd(a(n-1),n).

Source: https://oeis.org/A133058
Credit: @Solfanbtc

The recurrence `a(n) = a(n-1) + n + 1` if `gcd(a(n-1), n) = 1`, otherwise
`a(n) = a(n-1) / gcd(a(n-1), n)` ("Fly straight, dammit"); A133058 starts `a(0) = a(1) = 1` and
settles at `n = 638` into the loop `(1, x, 2x, 2)`.

Claim stated (Ctibor O. Zizka, Dec 26 2007, in the entry): for every choice of initial term
`a(0)`, there exist integers `r` and `t ≥ 0` [read: an `r` such that for all `t ≥ 0`] with
`a(2r+4t) = 1`, `a(2r+4t+1) = 2r+4t+3`, `a(2r+4t+2) = 2(2r+4t+3)`, `a(2r+4t+3) = 2`.
N. J. A. Sloane (Feb 22 2015) restates it and writes that he has not seen a proof. This is also
the case `R = 1` of Zizka's later (Oct 27 2015) conjecture on `a(n) = a(n-1) + n + R`, whose
other parts ("quasi-periodic" for `R ≤ 3`, not for `R ≥ 4`) use a notion the entry does not
define and are not stated here.

Reading of "every choice of initial term `a(0)`": `a(0)` is any positive integer and the
recurrence is applied for all `n ≥ 1` (if `a(1) = 1` were also kept fixed, `a(0)` would not
influence the sequence at all). A python3 check: for every `a(0) ≤ 300` the sequence enters the
loop within 20000 steps; and A133058 itself (with `a(1) = 1`) enters it at `n = 638`.

Conventions: `seq c n` is the sequence with `a(0) = c`.
-/

namespace OMA.S_oeis_a133058

/-- The recurrence with initial term `a(0) = c`, applied for all `n ≥ 1`. -/
def seq (c : ℕ) : ℕ → ℕ
  | 0 => c
  | n + 1 =>
      let x := seq c n
      if Nat.gcd x (n + 1) = 1 then x + (n + 1) + 1 else x / Nat.gcd x (n + 1)

/-- Zizka's claim: from every starting value the sequence enters the loop `(1, x, 2x, 2)`. -/
theorem main : ∀ c : ℕ, 1 ≤ c → ∃ r : ℕ, ∀ t : ℕ,
    seq c (2 * r + 4 * t) = 1 ∧ seq c (2 * r + 4 * t + 1) = 2 * r + 4 * t + 3 ∧
      seq c (2 * r + 4 * t + 2) = 2 * (2 * r + 4 * t + 3) ∧ seq c (2 * r + 4 * t + 3) = 2 := by
  sorry

end OMA.S_oeis_a133058
