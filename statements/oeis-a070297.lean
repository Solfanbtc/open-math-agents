import Mathlib

/-!
# A070297: Smallest number with n unrelated numbers (numbers which are neither coprime nor a divisor), or 0 if no such number exists.

Source: https://oeis.org/A070297
Credit: @Solfanbtc

Claim (OEIS entry, %C): "The 0's are only conjectures (search extended to 2000)." The listed zeros
are `a(2) = 0` and `a(13) = 0`: conjecturally no number has exactly 2, resp. 13, unrelated numbers.
We state, with the same strength as the data, that the listed terms `a(1), …, a(61)` are correct.

Conventions:
* `k` is unrelated to `m` when `1 ≤ k < m`, `k ∤ m` and `gcd(k, m) ≠ 1` (A045763).
* `a(n)` is the least `m` having exactly `n` unrelated numbers, or `0` if there is none (which is
  the value of `sInf ∅` in `ℕ`).
* `a(0)` is excluded: the data gives `a(0) = 3` (the PARI program only searches from `3`), the
  example says `a(0) = 4`, and the definition gives `a(0) = 1` (`1` has no unrelated numbers), so
  the entry is inconsistent at `n = 0`. For `n ≥ 1` the starting point of the search is
  irrelevant, since `1` and `2` have no unrelated numbers.
* Checked in Python for all `m ≤ 200000` (via `A045763(m) = m + 1 - d(m) - φ(m)`): the least
  `m` with exactly `n` unrelated numbers matches the data for `1 ≤ n ≤ 61`, and none has 2 or 13.
-/

namespace OMA.S_oeis_a070297

/-- The number of `k` with `1 ≤ k < m` that neither divide `m` nor are coprime to `m`. -/
def unrelatedCount (m : ℕ) : ℕ :=
  ((Finset.Ico 1 m).filter (fun k => ¬ k ∣ m ∧ Nat.gcd k m ≠ 1)).card

/-- `a(n)`: the least `m` with exactly `n` unrelated numbers, or `0` if none exists. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | unrelatedCount m = n}

/-- The listed terms `a(1), …, a(61)` of A070297 are correct (in particular `a(2) = a(13) = 0`). -/
theorem main :
    (List.range 61).map (fun i => a (i + 1)) =
      [6, 0, 10, 15, 14, 21, 18, 35, 22, 33, 26, 39, 0, 65, 30, 36, 38, 57, 44, 95, 46, 63, 42,
        115, 50, 64, 58, 87, 54, 75, 68, 155, 60, 99, 74, 111, 72, 185, 66, 117, 86, 129, 92,
        215, 94, 141, 78, 235, 84, 105, 98, 100, 96, 265, 90, 135, 118, 147, 122, 183, 108] := by
  sorry

end OMA.S_oeis_a070297
