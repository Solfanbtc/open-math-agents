import Mathlib

/-!
# A100661: Quet transform of A006519 (see A101387 for definition). Also, least k such that n+k has at most k ones in its binary representation.

Source: https://oeis.org/A100661
Credit: @Solfanbtc

Conjecture (Joerg Arndt, %e lines of A100661): `a(n)` is the number of bits (the number of
ones) in the binary words of sequence A108918, i.e. `a(n)` = number of ones of `A108918(n)`
(e.g. `A108918(5) = 7 = 111₂` and `a(5) = 3`).

Definitions.
* A100661 (offset 1), by its name: `a(n)` is the least `k` (`k ≥ 1`) such that `n + k` has at
  most `k` ones in binary. (This is the definition used by the SageMath program; the entry also
  computes it by greedy subtraction of Mersenne numbers, with the same values.)
* A108918, "reversed binary words in reversed lexicographic order": its first `2^k - 1` terms
  form the list `T_k` with `T_0 = []` and `T_{k+1} = T_k ++ (2^k + T_k) ++ [2^k]`
  (`1; 1,3,2; 1,3,2,5,7,6,4; ...`, as in the entry's listing of the words), so
  `A108918(n) = T_n[n - 1]` (`T_n` has `2^n - 1 ≥ n` entries).

Formalization. Writing `c(n)` for the number of ones of `A108918(n)`, the conjecture says that
`c(n)` is the least `k ≥ 1` with `popcount(n + k) ≤ k`, stated with `IsLeast`.

Checked with python3: `T_k` reproduces all listed terms of A108918, the least-`k` definition
reproduces all listed terms of A100661, and the conjecture holds for `1 ≤ n < 2^16`.
-/

namespace OMA.S_oeis_a100661

/-- Number of ones in the binary representation. -/
def popcount (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

/-- `blocks k` is the list of the first `2^k - 1` terms of A108918. -/
def blocks : ℕ → List ℕ
  | 0 => []
  | k + 1 => blocks k ++ (blocks k).map (2 ^ k + ·) ++ [2 ^ k]

/-- A108918 (offset 1). -/
def A108918 (n : ℕ) : ℕ := (blocks n).getD (n - 1) 0

/-- Arndt's conjecture: the number of ones of `A108918(n)` is the least `k ≥ 1` such that
`n + k` has at most `k` ones in binary, i.e. it equals A100661(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    IsLeast {k : ℕ | 1 ≤ k ∧ popcount (n + k) ≤ k} (popcount (A108918 n)) := by
  sorry

end OMA.S_oeis_a100661
