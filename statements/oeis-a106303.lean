import Mathlib

/-!
# A106303: Period of the Fibonacci 5-step sequence A001591 mod n.

Source: https://oeis.org/A106303
Credit: @Solfanbtc

Conjectures (Chai Wah Wu, Feb 25 2022, %F line of A106303):
1. `a(5^k) = 781 * 5^(k-1)` for `k > 0`;
2. for `p` prime, if `a(p) ≠ a(p^2)` then `a(p^k) = p^(k-1) * a(p)` for `k > 0`.

Formalization.
* `pent` is A001591 (offset 0): `0, 0, 0, 0, 1`, then each term is the sum of the previous
  five.
* `period n` is the period of `pent` modulo `n`: the least `k > 0` such that the window of five
  consecutive terms at position `k` is congruent mod `n` to the initial window
  `(0, 0, 0, 0, 1)`; this is the definition used by the programs in the entry. The set is
  nonempty for every `n ≥ 1` (finitely many windows mod `n`, and the recurrence can be run
  backwards since the coefficient of `a(n-5)` is `1`), so the window recurs and the sequence is
  purely periodic with this period.
* Both conjectures are stated as written, joined by `∧` (the first is the case `p = 5` of the
  second, given `a(5) = 781 ≠ 3905 = a(25)`).

Checked with python3: `period n` reproduces all listed %S/%T/%U terms (`n ≤ 38`); conjecture 1
holds for `k ≤ 3`, and conjecture 2 for `p ∈ {2, 3, 5, 7}`, `k ≤ 3` and `p ∈ {11, 13}`, `k ≤ 2`.
-/

namespace OMA.S_oeis_a106303

/-- A001591, the Fibonacci 5-step (pentanacci) numbers: `0, 0, 0, 0, 1, 1, 2, 4, 8, 16, 31, ...`. -/
def pent : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | n + 5 => pent n + pent (n + 1) + pent (n + 2) + pent (n + 3) + pent (n + 4)

/-- A106303: the period of `pent` modulo `n`. -/
noncomputable def period (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∀ i < 5, pent (k + i) ≡ pent i [MOD n]}

/-- Wu's two conjectures on `period` at prime powers. -/
theorem main :
    (∀ k : ℕ, 0 < k → period (5 ^ k) = 781 * 5 ^ (k - 1)) ∧
    (∀ p : ℕ, p.Prime → period p ≠ period (p ^ 2) →
      ∀ k : ℕ, 0 < k → period (p ^ k) = p ^ (k - 1) * period p) := by
  sorry

end OMA.S_oeis_a106303
