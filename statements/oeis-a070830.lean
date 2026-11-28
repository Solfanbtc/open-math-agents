import Mathlib

/-!
# A070830: Number of wide partitions of n.

Source: https://oeis.org/A070830
Credit: @Solfanbtc

Conjecture (the Wide Partition Conjecture of Chow, Fan, Goemans and Vondrák, "Wide partitions,
Latin tableaux, and Rota's basis conjecture", 2003; OEIS A070830, comment by N. J. A. Sloane,
Nov 21 2013: "still unsolved"): a partition is wide if and only if it has a Latin tableau.

Conventions:
* A partition λ = (λ_1 ≥ λ_2 ≥ ...) of n is its multiset of parts (`Nat.Partition n`), listed in
  decreasing order. λ' is the conjugate partition, λ'_k = #{i : λ_i ≥ k}.
* Wide: for every nonempty sub-multiset μ of the parts of λ, μ dominates its conjugate μ':
  μ_1 + ... + μ_t ≥ μ'_1 + ... + μ'_t for all t, where μ'_1 + ... + μ'_t = Σ_{x ∈ μ} min(x, t).
  This definition reproduces A070830 (1, 1, 2, 3, 3, 5, 6, 9, 11, 14, ... for n = 1..20).
* Latin tableau of shape λ: a filling of the Young diagram (row i, 0-indexed, has the cells
  (i, j), j < λ_{i+1}) with positive integers, no repeated entry in any row or column, in which
  each value k occurs exactly λ'_k times. With this convention, brute force for every partition of
  n ≤ 9 finds a Latin tableau exactly for the wide partitions. (The other convention, "k occurs
  λ_k times", already fails for λ = (2); it is the same notion for the transposed diagram.)
-/

namespace OMA.S_oeis_a070830

/-- The parts of a partition in decreasing order. -/
def desc {n : ℕ} (l : Nat.Partition n) : List ℕ := l.parts.sort (· ≥ ·)

/-- A multiset `μ` dominates its conjugate. -/
def DominatesConj (μ : Multiset ℕ) : Prop :=
  ∀ t : ℕ, (μ.map fun x => min x t).sum ≤ ((μ.sort (· ≥ ·)).take t).sum

/-- `λ` is wide: every nonempty sub-multiset of its parts dominates its conjugate. -/
def IsWide {n : ℕ} (l : Nat.Partition n) : Prop :=
  ∀ μ : Multiset ℕ, μ ≤ l.parts → μ ≠ 0 → DominatesConj μ

/-- The cells of the Young diagram of `λ`. -/
def cells {n : ℕ} (l : Nat.Partition n) : Finset (ℕ × ℕ) :=
  (Finset.range (desc l).length ×ˢ Finset.range (n + 1)).filter fun c => c.2 < (desc l).getD c.1 0

/-- `λ` has a Latin tableau. -/
def HasLatinTableau {n : ℕ} (l : Nat.Partition n) : Prop :=
  ∃ f : ℕ × ℕ → ℕ,
    (∀ c ∈ cells l, 1 ≤ f c) ∧
    (∀ c ∈ cells l, ∀ d ∈ cells l, c ≠ d → (c.1 = d.1 ∨ c.2 = d.2) → f c ≠ f d) ∧
    ∀ k : ℕ, 1 ≤ k →
      ((cells l).filter fun c => f c = k).card = (l.parts.filter fun x => k ≤ x).card

/-- The Wide Partition Conjecture. -/
theorem main : ∀ (n : ℕ) (l : Nat.Partition n), IsWide l ↔ HasLatinTableau l := by
  sorry

end OMA.S_oeis_a070830
