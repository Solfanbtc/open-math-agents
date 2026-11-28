import Mathlib

/-!
# A005840: Expansion of (1-x)*e^x/(2-e^x).

Source: https://oeis.org/A005840
Credit: @Solfanbtc

A005840 counts the labeled threshold graphs on `n` vertices. Conjecture (R. J. Mathar,
Apr 29 2019): "A285868 (with offset 1) shows the associated connected threshold graphs", that is,
for `n ≥ 1` the number of connected labeled threshold graphs on `n` vertices is `A285868(n - 1)`.

The entry also records (David Galvin, Oct 18 2021) that the number of connected labeled threshold
graphs on `n` vertices is A317057 (see also A053525), which differs from `A285868(n - 1)`. A brute
force count in Python gives connected counts 1, 1, 4, 23, 166, 1437 for `n = 1..6`, against
`A285868(n - 1)` = 1, 1, 4, 20, 126, 962. So the conjecture as stated appears to fail at `n = 4`,
and the statement below is expected to be disprovable. It is stated as the source states it.

Definitions:
* A graph on `Fin n` is a threshold graph if it can be built from the empty graph by adding the
  vertices one at a time, each new vertex being either isolated or dominating (adjacent to all
  earlier vertices). Here: there is an ordering `σ` of the vertices and a choice `dom` such that
  for `i < j`, `σ i` and `σ j` are adjacent iff the `j`-th vertex was added as dominating. This is
  the standard constructive characterization of threshold graphs (Chvátal and Hammer).
* A285868 is the row sums of A285867, `T(n, k) = S2(n, k) * k! + S2(n, k - 1) * (k - 1)!` with
  `S2(n, -1) = 0`; `S2` is `Nat.stirlingSecond`.
-/

namespace OMA.S_oeis_a005840

/-- `G` is a threshold graph: built by adding vertices one at a time, each isolated or
dominating. -/
def IsThreshold {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (σ : Fin n ≃ Fin n) (dom : Fin n → Bool), ∀ i j : Fin n, i < j →
    (G.Adj (σ i) (σ j) ↔ dom j = true)

/-- A285867: `T(n, k) = S2(n, k) k! + S2(n, k - 1) (k - 1)!`, the second term absent for `k = 0`. -/
def T (n k : ℕ) : ℕ :=
  Nat.stirlingSecond n k * k.factorial +
    (if k = 0 then 0 else Nat.stirlingSecond n (k - 1) * (k - 1).factorial)

/-- A285868: row sums of A285867. -/
def A285868 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- Mathar's conjecture: for `n ≥ 1`, the connected labeled threshold graphs on `n` vertices are
counted by `A285868(n - 1)`. -/
theorem main : ∀ n, 1 ≤ n →
    {G : SimpleGraph (Fin n) | IsThreshold G ∧ G.Connected}.ncard = A285868 (n - 1) := by
  sorry

end OMA.S_oeis_a005840
