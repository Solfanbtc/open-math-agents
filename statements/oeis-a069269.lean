import Mathlib

/-!
# A069269: Second level generalization of Catalan triangle (0th level is Pascal's triangle A007318; first level is Catalan triangle A009766; 3rd level is A069270).

Source: https://oeis.org/A069269
Credit: @Solfanbtc

The triangle (offset 0, rows `n ≥ 0`, `0 ≤ k ≤ n`) is `T(n, k) = C(n+2k, k)(n-k+1)/(n+k+1)`
(the `m = 2` case of the m-th level formula in the first comment; the division is exact).
Rows: 1; 1, 1; 1, 2, 3; 1, 3, 7, 12; ... (this reproduces every term of %S, %T, %U).

Conjecture (D. Callan, 2008): with offset 1 for `n` and `k`, i.e. for `1 ≤ k ≤ n` the entry
`T(n-1, k-1)`, this is the number of permutations of `[n]` that avoid the (classical) patterns
4231 and 42513 and whose last ascent ends at position `k` (`k = 1` if there are no ascents).
An ascent ending at position `i` (1-based) means `π(i-1) < π(i)` with `2 ≤ i ≤ n`.
Example from the entry: `T(4,3) = 7` counts 1243, 1342, 2143, 2341, 3142, 3241, 4132.
Checked by brute force for `n ≤ 8`.

Permutations of `[n]` are `Equiv.Perm (Fin n)` (positions and values 0-based); a permutation
contains a pattern when some subsequence has the same relative order as the pattern.
-/

namespace OMA.S_oeis_a069269

/-- A069269, offset 0. -/
def T (n k : ℕ) : ℕ := (n + 2 * k).choose k * (n - k + 1) / (n + k + 1)

/-- `σ` avoids the classical pattern given by the values `pattern`. -/
def Avoids {n m : ℕ} (σ : Equiv.Perm (Fin n)) (pattern : Fin m → ℕ) : Prop :=
  ¬ ∃ pos : Fin m → Fin n, StrictMono pos ∧
    ∀ i j, σ (pos i) < σ (pos j) ↔ pattern i < pattern j

/-- The 1-based position where the last ascent of `σ` ends, or `1` if `σ` has no ascent.
An ascent ends at the 0-based index `i` when `σ (i-1) < σ i`; its 1-based position is `i+1`. -/
def lastAscentEnd {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  max 1 ((Finset.univ.filter (fun i : Fin n => ∃ j : Fin n, j.val + 1 = i.val ∧ σ j < σ i)).sup
    (fun i => i.val + 1))

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    Nat.card {σ : Equiv.Perm (Fin n) //
      Avoids σ ![4, 2, 3, 1] ∧ Avoids σ ![4, 2, 5, 1, 3] ∧ lastAscentEnd σ = k} =
    T (n - 1) (k - 1) := by
  sorry

end OMA.S_oeis_a069269
