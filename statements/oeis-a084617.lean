import Mathlib

/-!
# A084617: Maximum number of circles with diameter 1 that can be packed in a square of side length n.

Source: https://oeis.org/A084617
Credit: @Solfanbtc

Data (offset 1): 1, 4, 9, 16, 25, 36, 49, 68, 86, 106, 128, 152, 181, 216, 247, 280.
"For n>5 the sequence terms are only conjectures." The entry claims these 16 values; stated
here as a(n) = data(n) for 1 ≤ n ≤ 16 (the part n ≤ 5 is claimed known).

Conventions: a packing of `m` disks of diameter 1 in the square `[0, n] × [0, n]` is a family of
centers `(x i, y i)` with `1/2 ≤ x i, y i ≤ n - 1/2` (each disk inside the square) and
`1 ≤ dist` between distinct centers (disjoint interiors). a(n) is the largest such `m` (bounded
by area, so `sSup` is the maximum).
-/

namespace OMA.S_oeis_a084617

/-- `m` disks of diameter 1 can be packed in the square of side `s`. -/
def Packable (s : ℝ) (m : ℕ) : Prop :=
  ∃ c : Fin m → EuclideanSpace ℝ (Fin 2),
    (∀ i, ∀ k, 1 / 2 ≤ c i k ∧ c i k ≤ s - 1 / 2) ∧ ∀ i j, i ≠ j → 1 ≤ dist (c i) (c j)

/-- A084617: maximum number of circles of diameter 1 that can be packed in a square of side `n`. -/
noncomputable def a (n : ℕ) : ℕ := sSup {m : ℕ | Packable n m}

/-- The terms a(1), ..., a(16) given in the entry. -/
def data : List ℕ := [1, 4, 9, 16, 25, 36, 49, 68, 86, 106, 128, 152, 181, 216, 247, 280]

theorem main : ∀ i : ℕ, (h : i < data.length) → a (i + 1) = data.get ⟨i, h⟩ := by
  sorry

end OMA.S_oeis_a084617
