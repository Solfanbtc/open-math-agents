import Mathlib

/-!
# A268642: Seelmann's sequence: a(1) = 1; thereafter a(n + 1) = ceiling(a(n)/2) unless this is already in the sequence, in which case a(n + 1) = 3*a(n).

Source: https://oeis.org/A268642
Credit: @Solfanbtc

Seelmann's sequence with multiplier `M`: `a(1) = 1`; thereafter `a(n+1) = ⌈a(n)/2⌉` unless this
is already in the sequence (among `a(1), ..., a(n)`), in which case `a(n+1) = M · a(n)`.
A268642 is the case `M = 3`: `1, 3, 2, 6, 18, 9, 5, 15, 8, 4, ...`.

Conjecture (the entry, corrected by Charlie Neder, Feb 06 2019): this is a permutation of the
positive integers, along with any Seelmann sequence for any integer `M > 1` not of the form
`M = 2^N`. Stated for all such `M` (the case `M = 3` included).

(For `M = 3`, the entry mentions a claimed proof on Reddit that N. J. A. Sloane had not checked.)

A python3 check: the definition reproduces the data for `M = 3`; for `M = 3, 5, 6, 7, 10, 12` the
first 300000 terms are distinct and contain every positive integer below 7300.

Conventions:
* `state M n` is the list `a(n+1), ..., a(1)` (newest first); `seel M n = a(n)` for `n ≥ 1`.
* `⌈x / 2⌉ = (x + 1) / 2` in `ℕ`.
-/

namespace OMA.S_oeis_a268642

/-- The terms `a(n+1), ..., a(1)` of the Seelmann sequence with multiplier `M`, newest first. -/
def state (M : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let L := state M n
      let cur := L.headD 0
      let c := (cur + 1) / 2
      (if L.contains c then M * cur else c) :: L

/-- `seel M n = a(n)` (`n ≥ 1`) for the Seelmann sequence with multiplier `M`. -/
def seel (M n : ℕ) : ℕ := (state M (n - 1)).headD 0

/-- Conjecture: for every `M > 1` that is not a power of 2, the Seelmann sequence with multiplier
`M` is a permutation of the positive integers (`M = 3` gives A268642). -/
theorem main : ∀ M : ℕ, 1 < M → (¬ ∃ N : ℕ, M = 2 ^ N) →
    Set.BijOn (seel M) {n | 1 ≤ n} {v | 1 ≤ v} := by
  sorry

end OMA.S_oeis_a268642
