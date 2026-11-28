import Mathlib

/-!
# A066400: Smallest values of t arising in R. L. Graham's sequence (A006255).

Source: https://oeis.org/A066400
Credit: @Solfanbtc

Graham's sequence A006255: `G(n)` is the smallest `m` for which there is a sequence
`n = b_1 < b_2 < … < b_t = m` with `b_1 b_2 ⋯ b_t` a perfect square. A strictly increasing
sequence from `n` to `m` is the same as a finite set `S` of integers with `min S = n` and
`max S = m`, and then `t = |S|`. A066400(n) is the smallest `t` for which such a sequence ending
at `m = G(n)` exists (e.g. `a(2) = 3`: `2, 3, 6`). Such a sequence exists for every `n ≥ 1`
(e.g. `G(n) ≤ 2n` for `n > 3`), so the infima below are attained.

Conjecture (Peter Kagey, 2016): `2` never appears in A066400, i.e. `a(n) ≠ 2` for all `n ≥ 1`
(equivalently, by the entry, `A006255(n) ≠ A072905(n)`). Checked with python3: the definitions
give the listed values of A006255 and A066400 for `n ≤ 30`.
-/

namespace OMA.S_oeis_a066400

/-- `S` is an admissible sequence from `n` to `m`: least element `n`, greatest element `m`,
product a perfect square. -/
def Admissible (n m : ℕ) (S : Finset ℕ) : Prop :=
  n ∈ S ∧ m ∈ S ∧ (∀ x ∈ S, n ≤ x ∧ x ≤ m) ∧ IsSquare (∏ x ∈ S, x)

/-- Graham's sequence A006255. -/
noncomputable def G (n : ℕ) : ℕ := sInf {m | ∃ S, Admissible n m S}

/-- A066400: the least length of an admissible sequence from `n` to `G n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {t | ∃ S, Admissible n (G n) S ∧ S.card = t}

/-- Kagey's conjecture: `2` never occurs in A066400. -/
theorem main : ∀ n : ℕ, 0 < n → a n ≠ 2 := by
  sorry

end OMA.S_oeis_a066400
