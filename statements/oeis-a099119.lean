import Mathlib

/-!
# A099119: Conjectured greatest k such that S(k) = S(k-n), or 0 if no k is known, where S is the Kempner function A002034.

Source: https://oeis.org/A099119
Credit: @Solfanbtc

`S(m)` (A002034) is the least positive integer `s` with `m ∣ s!` (`S(1) = 1`). For each
`n = 1, ..., 22` (the listed terms, offset 1), `a(n)` is the conjectured greatest `k` with
`S(k) = S(k - n)` (`k - n ≥ 1`), or `0` if no such `k` is known; T. D. Noe tested `k ≤ 10^8`.
The case `n = 1` (`a(1) = 0`, i.e. `S(k) ≠ S(k+1)` for all `k ≥ 1`) is Tutescu's conjecture.

Statement, for each listed `n`: every `k > n` with `S(k) = S(k - n)` satisfies `k ≤ a(n)`
(for `a(n) = 0` this says no such `k` exists), and when `a(n) ≠ 0` the value `k = a(n)` is
attained. Recomputed in Python for `k ≤ 3·10^5`: the last such `k` for `n = 1..22` matches
the data exactly.
-/

namespace OMA.S_oeis_a099119

/-- The Kempner function A002034: the least `s > 0` with `m ∣ s!`. -/
noncomputable def S (m : ℕ) : ℕ := sInf {s : ℕ | 0 < s ∧ m ∣ s.factorial}

/-- The listed terms `a(1), ..., a(22)`, as `data[n - 1]`. -/
def data : List ℕ :=
  [0, 18, 48, 12, 20, 0, 112, 1800, 45, 90, 2475, 48, 5005, 140, 30, 24, 69632, 90, 235144,
    60, 750, 4950]

theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 22 →
    (∀ k : ℕ, n < k → S k = S (k - n) → k ≤ data.getD (n - 1) 0) ∧
    (data.getD (n - 1) 0 ≠ 0 →
      S (data.getD (n - 1) 0) = S (data.getD (n - 1) 0 - n)) := by
  sorry

end OMA.S_oeis_a099119
