import Mathlib

/-!
# A079104: Number of permutations of length n containing the minimum number of monotone subsequences of length 4.

Source: https://oeis.org/A079104
Credit: @Solfanbtc

For a permutation `σ` of `Fin n`, a monotone subsequence of length 4 is a 4-element set of
positions on which `σ` is strictly increasing (ascending) or strictly decreasing (descending).
* A079104(n) (offset 1): the number of permutations of length `n` whose number of monotone
  subsequences of length 4 is the minimum over all permutations of length `n`.
* A079105(n) (offset 0): among the permutations of length `n` all of whose monotone subsequences
  of length 4 are descending, or all ascending (no ascending ones, or no descending ones), the
  number of those with the minimum number of such subsequences under that constraint.
(J. Myers, The minimum number of monotone subsequences, Electron. J. Combin. 9(2) (2002) #R4.)
Checked with python3 (brute force over all permutations, `n ≤ 9`): both definitions give the
listed data 1, 2, 6, 22, 86, 306, 882, 1764, 1764.

Conjecture (J. Myers, in the entry): A079104 equals A079105 from `a(17)` onwards (and so has
period 3, since A079105 is periodic with period 3 from its 15th term on: 1250, 3750, 3750, ...).
The listed values agree at `n = 17, 18` (3750, 1250) and differ at `n = 13, 16`.
`main`: for all `n ≥ 17`, A079104(n) = A079105(n).
-/

namespace OMA.S_oeis_a079104

open Classical

/-- Number of ascending subsequences of length 4 of `σ`. -/
noncomputable def asc4 {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun s : Finset (Fin n) =>
    s.card = 4 ∧ StrictMonoOn σ (s : Set (Fin n)))).card

/-- Number of descending subsequences of length 4 of `σ`. -/
noncomputable def desc4 {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun s : Finset (Fin n) =>
    s.card = 4 ∧ StrictAntiOn σ (s : Set (Fin n)))).card

/-- Number of monotone subsequences of length 4 of `σ`. -/
noncomputable def mono4 {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := asc4 σ + desc4 σ

/-- A079104(n). -/
noncomputable def A079104 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    ∀ τ : Equiv.Perm (Fin n), mono4 σ ≤ mono4 τ)).card

/-- Permutations whose monotone subsequences of length 4 are all descending or all ascending. -/
def OneSided {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop := asc4 σ = 0 ∨ desc4 σ = 0

/-- A079105(n). -/
noncomputable def A079105 (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    OneSided σ ∧ ∀ τ : Equiv.Perm (Fin n), OneSided τ → mono4 σ ≤ mono4 τ)).card

theorem main : ∀ n : ℕ, 17 ≤ n → A079104 n = A079105 n := by
  sorry

end OMA.S_oeis_a079104
