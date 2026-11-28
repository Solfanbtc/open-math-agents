import Mathlib

/-!
# A146304: Number of distinct ways to place bishops (up to 2n-2) on an n X n chessboard so that no bishop is attacking another and that it is not possible to add another bishop.

Source: https://oeis.org/A146304
Credit: @Solfanbtc

Conjecture (OEIS A146304, %F line): a(n) = O(n^(n-1)).

Definition: a(n) is the number of maximal independent sets of the n X n bishop graph (comment of
Eric W. Weisstein): sets S of squares, no two on a common diagonal or antidiagonal (bishops attack
along diagonals; on a set of pairwise non-attacking bishops blocking plays no role), such that every
square outside S shares a diagonal or antidiagonal with some square of S. Squares are
`Fin n × Fin n`; (i, j) and (k, l) share a diagonal iff i - j = k - l, an antidiagonal iff
i + j = k + l. ("Up to 2n-2" bishops is automatic.)
Checked numerically: brute force gives 1, 4, 10, 64 for n <= 4, as listed. Note: the listed terms
do not support the conjecture well: a(n)/n^(n-1) = 0.99, 1.17, 1.54, 2.25, 3.59, 6.25 at
n = 10, 12, 14, 16, 18, 20, still increasing; the statement is nevertheless the one in the entry.
-/

namespace OMA.S_oeis_a146304

open Filter Asymptotics

/-- Two distinct squares on a common diagonal or antidiagonal. -/
def Attacks {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p ≠ q ∧ (((p.1 : ℤ) - p.2 = (q.1 : ℤ) - q.2) ∨ ((p.1 : ℕ) + p.2 = (q.1 : ℕ) + q.2))

instance {n : ℕ} (p q : Fin n × Fin n) : Decidable (Attacks p q) := by
  unfold Attacks; infer_instance

/-- `S` is a maximal set of pairwise non-attacking bishops. -/
def IsMaximalPlacement {n : ℕ} (S : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ S, ∀ q ∈ S, ¬ Attacks p q) ∧ ∀ r, r ∉ S → ∃ p ∈ S, Attacks p r

instance {n : ℕ} (S : Finset (Fin n × Fin n)) : Decidable (IsMaximalPlacement S) := by
  unfold IsMaximalPlacement; infer_instance

/-- a(n): number of maximal non-attacking bishop placements on the n X n board. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n × Fin n) => IsMaximalPlacement S).card

theorem main : (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (n - 1)) := by
  sorry

end OMA.S_oeis_a146304
