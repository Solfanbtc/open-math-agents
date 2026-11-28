import Mathlib

/-!
# A014865: Numbers k that divide s(k), where s(1)=1, s(j)=15*s(j-1)+j.

Source: https://oeis.org/A014865
Credit: @Solfanbtc

`s(1) = 1`, `s(j) = 15 s(j-1) + j`; the sequence lists the `k ≥ 1` with `k ∣ s(k)`:
`1, 3, 5, 7, 15, 21, 35, 49, 55, 105, ...`.

Conjecture (Harvey P. Dale, Dec 04 2020, in the entry): all terms are odd, all terms greater than 7
are composite, and all terms greater than 1 are divisible by 3 or 5 or 7 (or some combination
thereof). Stated as the conjunction of the three claims, for every `k ≥ 1` with `k ∣ s(k)`.

A python3 check (via `s(k) = (15^{k+1} - 15(k+1) + k)/196`): the definition reproduces the
data, and the 151 terms up to `10⁶` satisfy all three claims.

Conventions: `s 0 = 0`, so that `s 1 = 15·0 + 1 = 1` and the recursion holds for all `j ≥ 1`.
"Composite" for `k > 7` is `¬ k.Prime` (such `k` are `> 1`).
-/

namespace OMA.S_oeis_a014865

/-- `s(j) = 15 s(j-1) + j`, `s(0) = 0` (so `s(1) = 1`). -/
def s : ℕ → ℕ
  | 0 => 0
  | j + 1 => 15 * s j + (j + 1)

/-- Dale's conjecture on the terms of A014865. -/
theorem main : ∀ k : ℕ, 1 ≤ k → k ∣ s k →
    Odd k ∧ (7 < k → ¬ k.Prime) ∧ (1 < k → 3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k) := by
  sorry

end OMA.S_oeis_a014865
