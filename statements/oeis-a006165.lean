import Mathlib

/-!
# A006165: Bala's nested-recurrence conjectures

Source: https://oeis.org/A006165
Credit: @Solfanbtc

A006165 (offset 1): `a(1) = a(2) = 1`; thereafter `a(2n+1) = a(n+1) + a(n)`, `a(2n) = 2a(n)`.
Data 1, 1, 2, 2, 3, 4, 4, 4, 5, 6, 7, 8, 8, …

Conjectures (P. Bala, Jul 31 2022), with `a^(1) = a` and `a^(k)(n) = a^(k-1)(a(n))`, i.e. the
`k`-fold iterate `a^[k]`. For `n ≥ 2`:
(i) `a(n) + a(n - a(n - a(n - a(n - a(n))))) = n`;
(ii) `a(n - a(n - a(n - a(n)))) = a(n - a(n - a(n - a(n - a(n - a(n))))))`;
(iii) `a^(2)(n) = a(n - a(n - a(n - a(n))))`;
(iv) `n - a(n) = a(n - a^(2)(n))`;
(v) `a(n - a(n)) = a^(2)(n - a^(2)(n - a^(2)(n - a^(2)(n))))`;
(vi) for `k ≥ 2`, `a^(k)(n - a^(k)(n)) = a^(k)(n - a^(k)(n - a^(k)(n - a^(k)(n))))`;
(vii) for `k ≥ 1`, the sequence `{n - a^(k)(n) : n ≥ 1}` has first differences 0 or 1.
"We conjecture that the repeated values of the sequence are of the form (2^k - 1)*2^m. The number
of repeated values appears to always be 2, 3, 5, 9, 17, 35, ..., independent of k, conjecturally
A000051." A000051 is `2^m + 1` (2, 3, 5, 9, 17, 33, …), and the entry's examples list the
multiplicities 2, 3, 5, 9, 17 for `3·2^m` and 2, 3, 5, 9 for `7·2^m`, so "35" is a slip for 33.
We read this as: every value taken more than once has the form `(2^k - 1) 2^m`, and the value
`(2^k - 1) 2^m` is taken exactly `2^m + 1` times.

Status: (vii) (the first-difference part) is proved in B. Yoo, Iterates and complete inverse
images for OEIS A006165: a proof of Bala's conjecture (vii), Zenodo (2026), cited in the entry;
`main` states all parts.

Conventions. `a 0 = 0` is a junk value outside the offset; for `n ≥ 2` no argument in (i)-(vi)
is ever `0`, and the subtractions in `ℕ` never truncate since `a(m) ≤ m` (checked with python3).
Checked with python3: all parts hold for `2 ≤ n < 5000` (`2 ≤ k ≤ 6` in (vi)), and the
repeated-value claims for `1 ≤ k ≤ 5` on that range (multiplicities 2, 3, 5, 9, 17, 33, …).
-/

namespace OMA.S_oeis_a006165

/-- A006165, with the junk value `a 0 = 0`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 =>
    if (n + 3) % 2 = 0 then 2 * a ((n + 3) / 2)
    else a ((n + 3) / 2 + 1) + a ((n + 3) / 2)
decreasing_by all_goals omega

/-- The number of `n ≥ 1` with `n - a^(k)(n) = v`. -/
noncomputable def mult (k v : ℕ) : ℕ := {n : ℕ | 1 ≤ n ∧ n - a^[k] n = v}.ncard

/-- Bala's conjectures (i)-(vii) for A006165. -/
theorem main :
    (∀ n, 2 ≤ n → a n + a (n - a (n - a (n - a (n - a n)))) = n) ∧
    (∀ n, 2 ≤ n → a (n - a (n - a (n - a n))) = a (n - a (n - a (n - a (n - a (n - a n)))))) ∧
    (∀ n, 2 ≤ n → a (a n) = a (n - a (n - a (n - a n)))) ∧
    (∀ n, 2 ≤ n → n - a n = a (n - a (a n))) ∧
    (∀ n, 2 ≤ n → a (n - a n) = a^[2] (n - a^[2] (n - a^[2] (n - a^[2] n)))) ∧
    (∀ k n, 2 ≤ k → 2 ≤ n →
      a^[k] (n - a^[k] n) = a^[k] (n - a^[k] (n - a^[k] (n - a^[k] n)))) ∧
    (∀ k, 1 ≤ k →
      (∀ n, 1 ≤ n → (n + 1) - a^[k] (n + 1) = n - a^[k] n ∨
        (n + 1) - a^[k] (n + 1) = n - a^[k] n + 1) ∧
      (∀ v, 2 ≤ mult k v → ∃ m, v = (2 ^ k - 1) * 2 ^ m) ∧
      (∀ m, mult k ((2 ^ k - 1) * 2 ^ m) = 2 ^ m + 1)) := by
  sorry

end OMA.S_oeis_a006165
