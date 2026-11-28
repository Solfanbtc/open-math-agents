import Mathlib

/-!
# A122437: Allowable values of the "dropping time" of the Collatz (3x+1) iteration.

Source: https://oeis.org/A122437 (cf. A060445, A126241, A020914)
Credit: @Solfanbtc

Here the Collatz map is `C(m) = m/2` for even `m`, `C(m) = 3m + 1` for odd `m` (the entry's
dropping times: `1` for even numbers, `6` for `3 → 10 → 5 → 16 → 8 → 4 → 2`). The dropping time
of `n` is the least `k ≥ 1` with `C^k(n) < n` (when it exists).

The allowable values are `a(j+1) = floor(1 + j + j log(3)/log(2))` (T. D. Noe), `j ≥ 0`:
`1, 3, 6, 8, 11, …`. Since `floor(j log₂ 3) = Nat.log 2 (3^j)`, this is
`a(j+1) = j + 1 + Nat.log 2 (3^j)` (= `A020914(j) + j`, K. Spage), the form used below (it
reproduces the listed data).

The entry says that only these numbers appear as dropping times (A060445) and, as clarified by
R. H. G. van Tol (Oct 11 2026), whether only these values occur depends on Terras's conjecture on
the coefficient stopping time (stated separately as `statements/oeis-a126241.lean`, which implies
the present claim). The conjecture stated here: every dropping time is an allowable value. Numbers
without a dropping time are not concerned. Checked numerically for `2 ≤ n < 2 · 10^6`.
-/

namespace OMA.S_oeis_a122437

/-- The Collatz map. -/
def collatz (m : ℕ) : ℕ := if m % 2 = 0 then m / 2 else 3 * m + 1

/-- `k` is the dropping time of `n`: the least `k ≥ 1` with `C^k(n) < n`. -/
def IsDroppingTime (n k : ℕ) : Prop :=
  1 ≤ k ∧ collatz^[k] n < n ∧ ∀ i, 1 ≤ i → i < k → n ≤ collatz^[i] n

/-- The allowable values `a(j+1) = j + 1 + floor(j log₂ 3)`, `j ≥ 0` (A122437). -/
def allowable (j : ℕ) : ℕ := j + 1 + Nat.log 2 (3 ^ j)

/-- Conjecture (OEIS A122437): every dropping time of the Collatz iteration is one of the
allowable values. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → IsDroppingTime n k → ∃ j, k = allowable j := by
  sorry

end OMA.S_oeis_a122437
