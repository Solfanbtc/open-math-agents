import Mathlib

/-!
# A091849: maximal size of an (n,4,2) optical orthogonal code

Source: https://oeis.org/A091849 (with https://oeis.org/A091848)
A091849(n) (offset 7) is the maximal size of an `(n,4,2)` optical orthogonal code (OOC); data for
`n = 7..23`: 1, 1, 1, 3, 3, 3, 4, 6, 7, 8, 9, 11, 12, 14, 15, 17, 18 (W. Chu and C. J. Colbourn,
Optimal (n,4,2)-OOC of small orders, Discrete Math. 279 (2004) 163-172).
A091848(n) is the Johnson bound `J(n,4,2) = ⌊(1/4) ⌊((n-1)/3) ⌊(n-2)/2⌋⌋⌋`
(PARI in the entry: `pr = (n-2)\2; pr = pr*(n-1)\3; pr\4`).
The entry says: "Conjectured to agree with A091848 except for n = 9 and 13."

An `(n,4,2)`-OOC is a family `𝒞` of 4-subsets of `ℤ/n` (the supports of weight-4 cyclic binary
sequences of length `n`) with auto-correlation `|C ∩ (C + t)| ≤ 2` for `C ∈ 𝒞`, `t ≢ 0`, and
cross-correlation `|C ∩ (C' + t)| ≤ 2` for distinct `C, C' ∈ 𝒞` and all `t`.

Minimal fix. Read literally, the comment is contradicted by the entry's own data at `n = 12`:
A091849(12) = 3 while A091848(12) = J(12,4,2) = 4. A python3 exhaustive search (maximum clique
over shift-orbits of admissible 4-subsets) confirms the data for `n = 7..16`: the maximum is
1, 1, 1, 3, 3, 3, 4, 6, 7, 8, against Johnson bounds 1, 1, 2, 3, 3, 4, 5, 6, 7, 8, so the
exceptions up to 16 are exactly 9, 12, 13. We therefore state the conjecture with the exception
set `{9, 12, 13}`: for every `n ≥ 7` outside it, the maximal size of an `(n,4,2)`-OOC equals
`J(n,4,2)` (some code has `J(n,4,2)` codewords, and none has more).

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a091849

/-- `𝒞` is an `(n,4,2)` optical orthogonal code. -/
def IsOOC (n : ℕ) (𝒞 : Finset (Finset (ZMod n))) : Prop :=
  (∀ C ∈ 𝒞, C.card = 4) ∧
  (∀ C ∈ 𝒞, ∀ t : ZMod n, t ≠ 0 → (C ∩ C.image (· + t)).card ≤ 2) ∧
  (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → ∀ t : ZMod n, (C ∩ C'.image (· + t)).card ≤ 2)

/-- A091848: the Johnson bound `J(n,4,2)`. -/
def johnson (n : ℕ) : ℕ := (n - 2) / 2 * (n - 1) / 3 / 4

theorem main : ∀ n : ℕ, 7 ≤ n → n ≠ 9 → n ≠ 12 → n ≠ 13 →
    (∃ 𝒞 : Finset (Finset (ZMod n)), IsOOC n 𝒞 ∧ 𝒞.card = johnson n) ∧
    (∀ 𝒞 : Finset (Finset (ZMod n)), IsOOC n 𝒞 → 𝒞.card ≤ johnson n) := by
  sorry

end OMA.S_oeis_a091849
