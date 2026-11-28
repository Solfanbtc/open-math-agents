import Mathlib

/-!
# A332077: Square array of sunflower numbers Sun(m,n)

Source: https://oeis.org/A332077
Credit: @Solfanbtc

`Sun(m, n)` (`m, n ≥ 1`) is the minimal number of distinct sets of cardinality `≤ m` such that
there is a sunflower with at least `n` sets among them: every family of `Sun(m, n)` distinct sets
of cardinality `≤ m` contains a sunflower of `≥ n` sets, and `Sun(m, n)` is least with this
property. A sunflower is a collection of sets all of whose pairwise intersections of distinct
members are equal. (The entry uses "at least n", following Tao; other authors use
`f(k, r) = Sun(k, r) - 1`.)

Sunflower conjecture, in the form of the entry: `Sun(m, n) ≤ (n · O(1))^m`, i.e. there is an
absolute constant `C` with `Sun(m, n) ≤ (C n)^m` for all `m, n ≥ 1`.

This is stronger than the upstream `Erdos20.erdos_20` (`f n k < (c k)^n` with a constant `c k`
depending on the number of petals): here the dependence on the number `n` of petals is linear,
with a single constant `C`.

Conventions:
* Sets are finite sets of natural numbers (a finite family of finite sets over any ground set
  embeds into `ℕ`), families are `Finset (Finset ℕ)`, hence of distinct sets.
* Sanity checks (python3): with this definition `Sun(1, n) = n`, and `Sun(2, 3) = 7`, matching the
  entry's formula `Sun(2, n) = n(n - 1) + 1` for odd `n` (two disjoint triangles give 6 edges with
  no 3-sunflower; every 7 sets of size `≤ 2` on 5 points contain one).
-/

namespace OMA.S_oeis_a332077

/-- `S` is a sunflower: all intersections of two distinct members coincide. -/
def IsSunflower (S : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ∀ C ∈ S, ∀ D ∈ S, C ≠ D → A ∩ B = C ∩ D

/-- `Sun m n`: the least `N` such that every family of at least `N` distinct sets of cardinality
`≤ m` contains a sunflower with at least `n` sets. -/
noncomputable def Sun (m n : ℕ) : ℕ :=
  sInf {N | ∀ F : Finset (Finset ℕ), (∀ A ∈ F, A.card ≤ m) → N ≤ F.card →
    ∃ S ⊆ F, n ≤ S.card ∧ IsSunflower S}

/-- Sunflower conjecture: `Sun(m, n) ≤ (n · O(1))^m`. -/
theorem main : ∃ C : ℝ, ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → (Sun m n : ℝ) ≤ (C * n) ^ m := by
  sorry

end OMA.S_oeis_a332077
