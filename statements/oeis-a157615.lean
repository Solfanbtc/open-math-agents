import Mathlib

/-!
# A157615: On an n X n board, a(n) is the maximal number of squares covered by a self-avoiding path made of alternated vertical and horizontal unitary steps.

Source: https://oeis.org/A157615
Credit: @Solfanbtc

Conjecture (OEIS A157615, comment): David Wilson conjectures that the formula for a(n) is
a(1)=1, then, a(n)=n^2-n+2 for n even, and a(n)=n^2-2n+4 for n>1 odd.

Conventions:
* The squares of the n X n board are the cells `(x, y)` with `0 ≤ x, y < n`. A path of `k`
  squares is a list `p 0, ..., p (k-1)` of pairwise distinct cells (self-avoiding) where each
  step `p (i+1) - p i` is a unit step, horizontal `(±1, 0)` or vertical `(0, ±1)`, and
  horizontal and vertical steps alternate. A single square (k = 1) is a path.
* a(n) is the greatest `k` for which such a path exists (`IsGreatest`).
* Checked by exhaustive search in Python: this gives a(1..6) = 1, 4, 7, 14, 19, 32, equal
  to the data and to the formula.
-/

namespace OMA.S_oeis_a157615

/-- The step from `p i` to `p (i+1)` is horizontal. -/
def IsHorizStep (p : ℕ → ℤ × ℤ) (i : ℕ) : Prop :=
  (p (i + 1)).2 = (p i).2 ∧ ((p (i + 1)).1 = (p i).1 + 1 ∨ (p (i + 1)).1 + 1 = (p i).1)

/-- The step from `p i` to `p (i+1)` is vertical. -/
def IsVertStep (p : ℕ → ℤ × ℤ) (i : ℕ) : Prop :=
  (p (i + 1)).1 = (p i).1 ∧ ((p (i + 1)).2 = (p i).2 + 1 ∨ (p (i + 1)).2 + 1 = (p i).2)

/-- `p 0, ..., p (k-1)` is a self-avoiding path of `k` squares on the `n × n` board made of
alternating horizontal and vertical unit steps. -/
def IsAltPath (n k : ℕ) (p : ℕ → ℤ × ℤ) : Prop :=
  1 ≤ k ∧
  (∀ i < k, 0 ≤ (p i).1 ∧ (p i).1 < n ∧ 0 ≤ (p i).2 ∧ (p i).2 < n) ∧
  (∀ i < k, ∀ j < k, p i = p j → i = j) ∧
  (∀ i, i + 1 < k → IsHorizStep p i ∨ IsVertStep p i) ∧
  (∀ i, i + 2 < k → (IsHorizStep p i ↔ IsVertStep p (i + 1)))

/-- Wilson's formula. -/
def wilson (n : ℕ) : ℕ :=
  if n = 1 then 1 else if Even n then n ^ 2 - n + 2 else n ^ 2 - 2 * n + 4

/-- Wilson's conjecture: for every `n ≥ 1`, the maximal number of squares covered by such a
path on the `n × n` board is given by the formula. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    IsGreatest {k : ℕ | ∃ p : ℕ → ℤ × ℤ, IsAltPath n k p} (wilson n) := by
  sorry

end OMA.S_oeis_a157615
