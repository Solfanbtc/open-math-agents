import Mathlib

/-!
# A132990: Trajectory of 11 under map n -> A132988(n).

Source: https://oeis.org/A132990
Credit: @Solfanbtc

A132988 (offset 1): `A132988(n)` is the smallest `k` not occurring earlier (among
`A132988(1), ..., A132988(n-1)`) such that `k` divides `prime(n) + 1`.
A132990 (offset 0) is the trajectory of `11` under `n ↦ A132988(n)`:
`a(0) = 11`, `a(i+1) = A132988(a(i))`.

Conjecture (OEIS A132990, K. Brockhaus): the sequence is not periodic.

Notes on the model.
* `prime(n)` (1-indexed, `prime(1) = 2`) is `Nat.nth Nat.Prime (n - 1)`.
* The smallest admissible `k` is searched in `[1, prime(n) + 1]`; this loses nothing, since every
  divisor of `prime(n) + 1` lies there, and `prime(n) + 1` itself is always admissible (an earlier
  value divides `prime(m) + 1 < prime(n) + 1`), so the default `0` of `find?` is never used.
* The values of `A132988` are pairwise distinct by construction, so the map is injective, and the
  trajectory is eventually periodic iff it is purely periodic; we state the literal claim
  "there is no period `T > 0` with `a(i + T) = a(i)` for all `i`".
* Checked with python3: this definition reproduces all 62 terms of the OEIS data
  11, 16, 18, 31, 32, 33, 23, 21, 37, 79, ..., 116, 107, 147, 122, and the first 71 terms of A132988.
-/

namespace OMA.S_oeis_a132990

/-- `firstValues n = [A132988(1), ..., A132988(n)]`. -/
noncomputable def firstValues : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let L := firstValues n
    let p := Nat.nth Nat.Prime n
    L ++ [((List.range' 1 (p + 1)).find? (fun k => decide (k ∣ p + 1 ∧ k ∉ L))).getD 0]

/-- `A132988 n` for `n ≥ 1`: the smallest `k` not occurring earlier with `k ∣ prime(n) + 1`. -/
noncomputable def A132988 (n : ℕ) : ℕ := (firstValues n).getD (n - 1) 0

/-- A132990: the trajectory of `11` under `n ↦ A132988(n)`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 11
  | i + 1 => A132988 (a i)

/-- Conjecture: the trajectory of 11 under `A132988` is not periodic. -/
theorem main : ¬ ∃ T : ℕ, 0 < T ∧ ∀ i : ℕ, a (i + T) = a i := by
  sorry

end OMA.S_oeis_a132990
