import Mathlib

/-!
# A109037: irreducible partitions into triangular numbers

Source: https://oeis.org/A109037
`a(n)` (offset 0) is the number of irreducible partitions of `n` into triangular numbers, where a
partition is irreducible if no subpartition with 2 or more parts sums to a triangular number
(e.g. `a(9) = 1`, for `[6,3]`). Data: 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, ...
The entry: "Sequence is almost certainly unbounded. Obviously it contains infinitely many 1's,
at triangular indices. At non-triangular indices, series appears to go to infinity, but this is
conjecture and growth rate is entirely unknown. Also unknown is whether the sequence is onto the
positive integers."

We state the two conjectures, as a conjunction: (1) `a` is unbounded, and (2) `a(n) → ∞` as `n`
runs through the non-triangular numbers (for every `M` there is `N` such that `a(n) ≥ M` for
every non-triangular `n ≥ N`). (2) implies (1); both are stated, as in the source. Surjectivity is
only called "unknown" in the entry, not conjectured, so it is not stated.

Conventions. Parts are positive triangular numbers `k(k+1)/2` (1, 3, 6, 10, ...); subpartitions
are sub-multisets of the parts, including the whole partition. Triangular numbers include 0,
which never matters here (a subpartition with `≥ 2` positive parts has sum `≥ 2`).
Checked: an `#eval` of this Lean definition gives `a(0..12) = 1, ..., 1, 2`, and an independent
python3 count reproduces all 96 listed terms `a(0..95)`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a109037

/-- `m` is a triangular number `k(k+1)/2` (the bound `k ≤ m` loses nothing). -/
def IsTriangular (m : ℕ) : Prop := ∃ k ∈ Finset.range (m + 1), k * (k + 1) / 2 = m

instance : DecidablePred IsTriangular := fun m => by unfold IsTriangular; infer_instance

/-- `P` is a partition into triangular numbers no subpartition of which, with at least two
parts, sums to a triangular number. -/
def Irred {n : ℕ} (P : n.Partition) : Prop :=
  (∀ x ∈ P.parts, IsTriangular x) ∧
    ∀ s ∈ P.parts.powerset, 2 ≤ Multiset.card s → ¬ IsTriangular s.sum

instance {n : ℕ} : DecidablePred (@Irred n) := fun P => by
  unfold Irred; infer_instance

/-- A109037: the number of irreducible partitions of `n` into triangular numbers. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun P : n.Partition => Irred P)).card

theorem main :
    (∀ M : ℕ, ∃ n : ℕ, M ≤ a n) ∧
    (∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ IsTriangular n → M ≤ a n) := by
  sorry

end OMA.S_oeis_a109037
