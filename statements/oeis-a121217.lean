import Mathlib

/-!
# A121217: the lag-two EKG sequence is a permutation of the positive integers

Source: https://oeis.org/A121217
`a(1) = 1`, `a(2) = 2`, `a(3) = 3`; for `n > 3`, `a(n)` is the smallest positive integer which
does not occur earlier in the sequence and which is not coprime to `a(n-2)`:
1, 2, 3, 4, 6, 8, 9, 10, 12, 5, 14, 15, 7, 18, ...
Conjecture (Reinhard Zumkeller, Apr 05 2015): "this is a permutation of the positive integers".
(A 2026 note by Tomer Haver, Zenodo doi:10.5281/zenodo.23437539, linked from the entry, claims a
proof; the statement is given faithfully regardless.)

We state: `n ↦ a(n)` is injective on `n ≥ 1` and takes every positive integer value.
Conventions. `terms n = [a(1), ..., a(n)]`; each new term is an `sInf` (it exists, since
`a(n-2) ≥ 2` for `n ≥ 4` and its multiples not yet used are admissible).
Checked with `#eval` (bounded search): `a(1..72)` agree with the listed terms.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a121217

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | 3 => [1, 2, 3]
  | n + 4 =>
    let l := terms (n + 3)
    l ++ [sInf {k : ℕ | 1 ≤ k ∧ k ∉ l ∧ 1 < Nat.gcd k (l.getD (n + 1) 0)}]

/-- A121217: `a(n)`, `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

theorem main :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → a m = a n → m = n) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, 1 ≤ n ∧ a n = k) := by
  sorry

end OMA.S_oeis_a121217
