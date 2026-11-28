import Mathlib

/-!
# A173419: Length of shortest computation yielding n using addition, subtraction and multiplication (starting from 1).

Source: https://oeis.org/A173419
Credit: @Solfanbtc

OEIS definition: let `x_0 = 1` and `x_m = n`, with each `x_k = x_i + x_j`, `x_k = x_i * x_j` or
`x_k = x_i - x_j` for some `0 ≤ i, j < k`. `a(n)` is the least such `m` (offset 1).

Intermediate values are integers (subtraction may go below zero) and are not bounded, as in the
OEIS comment. `a n` is defined as `sInf` of the set of admissible lengths; for `n ≥ 1` this set is
nonempty (`x_k = k + 1` reaches `n` in `n - 1` steps), so `sInf` is the true minimum on the
sequence's domain. With this model, an exhaustive search reproduces all 108 data terms
`a(1..108) = 0, 1, 2, 2, 3, 3, 4, 3, 3, 4, ...`.

Conjecture (Dmitry Kamenetsky, Dec 26 2019, OEIS comment): if `n` is prime then
`a(n) ≥ a(n-1)`. Checked there for `n < 1800`.

Status: the conjecture is FALSE. Rosario Patanè (OEIS comment, Aug 28 2026; "Counterexamples to a
conjecture of Kamenetsky on OEIS A173419", hal-05756029, 2026) shows it fails at `p = 3359`:
`a(3359) = 7 < 8 = a(3358)`, via `1, 2, 4, 16, 15, 225, 3375, 3359` (`3359 = 15^3 - 16`).
The other counterexamples below 5000 are `p = 3623, 4909, 4943`. The conjecture is stated here
faithfully, as the source states it.
-/

namespace OMA.S_oeis_a173419

/-- `Computes m n`: there is a computation `x_0 = 1, x_1, …, x_m = n` in which every `x_k`
(`0 < k ≤ m`) is `x_i + x_j`, `x_i - x_j` or `x_i * x_j` for some `i, j < k`. -/
def Computes (m : ℕ) (n : ℤ) : Prop :=
  ∃ x : ℕ → ℤ, x 0 = 1 ∧ x m = n ∧
    ∀ k, 0 < k → k ≤ m → ∃ i < k, ∃ j < k,
      x k = x i + x j ∨ x k = x i - x j ∨ x k = x i * x j

/-- A173419: the length of a shortest such computation yielding `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | Computes m (n : ℤ)}

/-- Kamenetsky's conjecture: for every prime `n`, `a(n) ≥ a(n - 1)`.
(Disproved: `n = 3359` is a counterexample, see the module docstring.) -/
theorem main : ∀ n : ℕ, n.Prime → a (n - 1) ≤ a n := by
  sorry

end OMA.S_oeis_a173419
