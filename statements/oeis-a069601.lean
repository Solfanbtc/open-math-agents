import Mathlib

/-!
# A069601: Smallest triangular number containing all the digits of numbers from 1 to n.

Source: https://oeis.org/A069601
Credit: @Solfanbtc

"Containing all the digits of numbers from 1 to n" is read with multiplicity: the multiset `D n`
of base-10 digits of `1, 2, …, n` must be a sub-multiset of the digits of the triangular number.
The entry says so explicitly: "For a(10) and higher, all duplicated digits must be in the term"
(below 10 the digits of `1, …, n` are distinct anyway). `a(n)` is the least triangular number
`t = m (m + 1) / 2` with `D n ≤ digits t`. Checked with python3 for `n ≤ 11`: this gives exactly
the data 1, 21, 231, 12403, 24531, 235641, ... (The example's value 219453 for `a(5)` is not
minimal: `24531 = T(221)` is smaller and is the listed term.)

Conjecture (Chai Wah Wu, 2020): except for `a(4) = 12403` (an extra digit 0), the digits of `a(n)`
are exactly the digits of the numbers from 1 to `n`, i.e. the digit multisets are equal.
`main` states it for all `n ≥ 1`, `n ≠ 4` (python3: true for `n ≤ 11`, false at `n = 4`).
-/

namespace OMA.S_oeis_a069601

/-- Multiset of the base-10 digits of `1, 2, …, n`. -/
def D (n : ℕ) : Multiset ℕ := ∑ k ∈ Finset.Icc 1 n, ((Nat.digits 10 k : List ℕ) : Multiset ℕ)

/-- Multiset of the base-10 digits of `t`. -/
def digitMs (t : ℕ) : Multiset ℕ := ((Nat.digits 10 t : List ℕ) : Multiset ℕ)

/-- Triangular numbers containing all the digits of `1, …, n` (with multiplicity). -/
def Candidates (n : ℕ) : Set ℕ := {t | (∃ m : ℕ, t = m * (m + 1) / 2) ∧ D n ≤ digitMs t}

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 4 → ∀ t : ℕ, IsLeast (Candidates n) t → digitMs t = D n := by
  sorry

end OMA.S_oeis_a069601
