import Mathlib

/-!
# A069187: Numbers k such that core(k) = ceiling(sqrt(k)).

Source: https://oeis.org/A069187
Credit: @Solfanbtc

`core(k)` is the squarefree part of `k`: the smallest positive integer `c` such that `k c` is a
square. A069187 lists the `k ≥ 1` with `core(k) = ⌈√k⌉`: `1, 2, 20, 90, 272, 650, 1332, 4160, ...`.

Conjecture (Ralf Stephan, Aug 18 2004, in the entry): the sequence is A071253 (`n^2 (n^2 + 1)`,
`n ≥ 0`) minus the entries whose index `n` is in A049532 (`n^2 + 1` not squarefree); i.e. the
terms are the `n^2 (n^2 + 1)` with `n^2 + 1` squarefree.

Minimal fix, explained: read literally the set equality fails at trivial values: `1` is a term
of A069187 (`core(1) = 1 = ⌈√1⌉`) but not of A071253, and `0 = A071253(0)` (with `0^2 + 1 = 1`
squarefree) is not a term (A069187 lists positive `k`). So it is stated for `k ≥ 2`, with `n ≥ 1`:
`core(k) = ⌈√k⌉` iff `k = n^2 (n^2 + 1)` for some `n ≥ 1` with `n^2 + 1` squarefree.
(One direction is elementary; the content is the converse.)

A python3 check (sieve for `core` up to `10^7`): the definition reproduces the data, and the
terms `k ≥ 2` up to `10^7` are exactly the 50 numbers `n^2 (n^2 + 1) ≤ 10^7` with `n^2 + 1`
squarefree (e.g. `2450 = 7^2 · 50` is excluded).
-/

namespace OMA.S_oeis_a069187

/-- `core k`: the smallest positive `c` such that `k c` is a square. -/
noncomputable def core (k : ℕ) : ℕ := sInf {c : ℕ | 1 ≤ c ∧ IsSquare (k * c)}

/-- Stephan's conjecture (for `k ≥ 2`, see the docstring). -/
theorem main : ∀ k : ℕ, 2 ≤ k →
    (core k = ⌈Real.sqrt k⌉₊ ↔
      ∃ n : ℕ, 1 ≤ n ∧ Squarefree (n ^ 2 + 1) ∧ k = n ^ 2 * (n ^ 2 + 1)) := by
  sorry

end OMA.S_oeis_a069187
