import Mathlib

/-!
# A116674: odd partitions with k distinct parts vs strict partitions with k maximal runs

Source: https://oeis.org/A116674
`T(n,k)` (`n ≥ 1`, `k ≥ 1`) is the number of partitions of `n` into odd parts having exactly `k`
distinct parts. Conjecture (Gus Wiseman, Jun 24 2025): `T(n,k)` is "also the number of strict
integer partitions of n with k maximal runs of consecutive parts decreasing by 1".
(Row 9: `T(9,·) = 3, 4, 1`; the strict partitions (9), (5,4), (4,3,2) have one run; (6,3), (7,2),
(8,1), (6,2,1) have two; (5,3,1) has three.)

Status: this is Sylvester's refinement of Euler's odd/distinct partition theorem (J. J.
Sylvester, 1882); see e.g. M. B. Nathanson, arXiv:1601.07058, Theorem 10. It is stated
faithfully as the entry gives it.

Formalization. Partitions are Mathlib's `Nat.Partition`; `Nat.Partition.odds n` are those with
all parts odd and `Nat.Partition.distincts n` the strict ones. The number of distinct parts is
the card of `parts.toFinset`. In a strict partition each maximal run of consecutive integers has
exactly one largest element `x`, the one with `x + 1` not a part, so the number of maximal runs
is the number of parts `x` with `x + 1` not a part.
Checked with python3: both counts agree for all `1 ≤ n ≤ 40` and all `k`, and reproduce the 86
listed terms.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a116674

/-- The number of maximal runs of consecutive parts of a strict partition. -/
def runs {n : ℕ} (p : n.Partition) : ℕ :=
  (p.parts.toFinset.filter (fun x => x + 1 ∉ p.parts)).card

theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((Nat.Partition.odds n).filter (fun p => p.parts.toFinset.card = k)).card =
      ((Nat.Partition.distincts n).filter (fun p => runs p = k)).card := by
  sorry

end OMA.S_oeis_a116674
