import Mathlib

/-!
# A022558: Number of permutations of length n avoiding the pattern 1342

Source: https://oeis.org/A022558
Credit: @Solfanbtc

Conjecture (Alexander Burstein, Mar 21 2019, in the entry): `a(n)` is the number of
permutations of length `n` simultaneously avoiding the patterns `2143` and `415263`.

Conventions:
* `a(n)` is, by the entry's name, the number of permutations of length `n` avoiding the
  (classical, not consecutive) pattern `1342`; the offset is 0 and `a(0) = 1` counts the empty
  permutation.
* A permutation `σ` of `Fin n` contains a pattern `p` of length `k` when there are positions
  `i₀ < i₁ < ⋯ < i_{k-1}` such that `σ(i_a) < σ(i_b) ↔ p_a < p_b` for all `a, b`; it avoids
  `p` otherwise.
* The conjecture is stated for every `n` (including `n = 0`); a brute-force check in Python
  confirms equality for `n ≤ 8` (`1, 1, 2, 6, 23, 103, 512, 2740, 15485`).
-/

namespace OMA.S_oeis_a022558

/-- `σ` avoids the classical pattern `pattern` (given by its one-line notation). -/
def Avoids {n k : ℕ} (σ : Equiv.Perm (Fin n)) (pattern : Fin k → ℕ) : Prop :=
  ¬ ∃ positions : Fin k → Fin n, StrictMono positions ∧
    ∀ i j, σ (positions i) < σ (positions j) ↔ pattern i < pattern j

/-- OEIS A022558: the number of permutations of length `n` avoiding `1342`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) // Avoids σ ![1, 3, 4, 2]}

/-- Burstein's conjecture: `a(n)` is the number of permutations of length `n` avoiding both
`2143` and `415263`. -/
theorem main : ∀ n : ℕ,
    Nat.card {σ : Equiv.Perm (Fin n) //
      Avoids σ ![2, 1, 4, 3] ∧ Avoids σ ![4, 1, 5, 2, 6, 3]} = a n := by
  sorry

end OMA.S_oeis_a022558
