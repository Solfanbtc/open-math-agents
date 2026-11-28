import Mathlib

/-!
# A069199: A Collatz-Fibonacci mixture.

Source: https://oeis.org/A069199
Credit: @Solfanbtc

`a(1) = 1`, `a(2) = 7`, and with `s = a(n+1) + a(n)`: `a(n+2) = s/3` if `3 ∣ s`; otherwise
`a(n+2) = s/2` if `2 ∣ s`; otherwise `a(n+2) = s` (the rules apply in this order: e.g.
`8 + 13 = 21 ↦ 7`). Data: `1, 7, 4, 11, 5, 8, 13, 7, 10, 17, ...`.

Conjecture (Benoit Cloitre, in the entry; "Does this sequence diverge to infinity?"): with
`a(1) = 1` and `a(2) = m`: if `m = 2` the sequence is constant `= 1`, if `m = 5` it is cyclic,
and for every other `m` it diverges.

Minimal fixes, explained:
* `m = 1` gives `1, 1, 1, ...` (constant, `1 + 1 = 2 ↦ 1`), so "diverges for every `m ≠ 2, 5`"
  fails at this trivial value; the divergence claim is stated for `m ≥ 3`, `m ≠ 5`.
* For `m = 2` the sequence is `1, 2, 1, 1, 1, ...`: constant `1` from `a(3)` on.
* For `m = 5` the sequence is `1, 5, 2, 7, 3, 5, 4, 3, 7, 5, 4, 3, 7, ...`: the entry's cycle
  "(5, 2, 7, 3)" lists its first terms, but the actual cycle is `(5, 4, 3, 7)`, from `a(6)` on;
  stated as `a(n+4) = a(n)` for `n ≥ 6`.
"Diverges" (to infinity) is `a(n) → ∞`.

A python3 check: the rule reproduces the data; for `1 ≤ m ≤ 3000` the terms `a(1401..1500)` all
exceed `10^12` except for `m ∈ {1, 2, 5}`; the `m = 2` and `m = 5` claims hold as stated.

Conventions: `seq m k = a(k+1)` for the start `a(1) = 1`, `a(2) = m`; `a m n = seq m (n - 1)`.
-/

namespace OMA.S_oeis_a069199

open Filter

/-- One step of the rule applied to `s = a(n+1) + a(n)`. -/
def step (s : ℕ) : ℕ := if s % 3 = 0 then s / 3 else if s % 2 = 0 then s / 2 else s

/-- `pair m k = (a(k+1), a(k+2))` for `a(1) = 1`, `a(2) = m`. -/
def pair (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, m)
  | k + 1 => ((pair m k).2, step ((pair m k).1 + (pair m k).2))

/-- `a m n = a(n)` (`n ≥ 1`) for the start `a(1) = 1`, `a(2) = m`. -/
def a (m n : ℕ) : ℕ := (pair m (n - 1)).1

/-- Cloitre's conjecture (with the fixes explained in the docstring). The sequence A069199
itself is the case `m = 7`. -/
theorem main : (∀ n : ℕ, 3 ≤ n → a 2 n = 1) ∧
    (∀ n : ℕ, 6 ≤ n → a 5 (n + 4) = a 5 n) ∧
    (∀ m : ℕ, 3 ≤ m → m ≠ 5 → Tendsto (a m) atTop atTop) := by
  sorry

end OMA.S_oeis_a069199
