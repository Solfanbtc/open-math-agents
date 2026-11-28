import Mathlib

/-!
# A036559: Squared distances that cannot arise in any Barlow packing

Source: https://oeis.org/A036559
Credit: @Solfanbtc

Squared distances that cannot arise in any Barlow packing of spheres of diameter `√3` (the scale
making all squared distances integers): `1, 2, 4, 5, 7, 10, 13, 14, 16, 23, …`. Complement of
A036558.

Model. A Barlow packing is a stacking of hexagonal layers of touching spheres, each layer in one
of the three positions `A, B, C`, consecutive layers in different positions. In-plane positions
are Eisenstein integers `a + bω` (`ω = e^(2πi/3)`, squared norm `a^2 - ab + b^2`); the three
cosets of the sublattice `(1 - ω)ℤ[ω]` (index 3; `a + bω ↦ a + b mod 3`) are the positions
`A, B, C`. Each coset is a triangular lattice of spacing `√3` (spheres of diameter `√3` touching
in a layer), points of different cosets are at distance `≥ 1`, and adjacent layers are at height
`√2` (a sphere on three spheres below: `1 + h^2 = 3`). So a packing is `s : ℤ → ZMod 3` with
`s (i+1) ≠ s i`, its sphere centres are the `(i, a, b)` with `a + b ≡ s i (mod 3)`, and the
squared distance between `(i, a, b)` and `(j, c, d)` is
`(a-c)^2 - (a-c)(b-d) + (b-d)^2 + 2 (i-j)^2`. `D ∈ A036559` iff `D ≥ 1` and no Barlow packing has
two centres at squared distance `D`. (With this model a Python computation reproduces all 55
data terms.)

Conjecture (J. H. Conway, N. J. A. Sloane, OEIS formula): the sequence consists of the numbers
`4^n · 1`, `4^n · 7`, `4^n · 13`, `4^n · (16k + 10)` (`n, k ≥ 0`) together with
`2, 5, 14, 23, 38, 230`. (Python: agrees for `D ≤ 5000`.)
-/

namespace OMA.S_oeis_a036559

/-- A Barlow stacking: consecutive layers in different positions. -/
def IsBarlow (s : ℤ → ZMod 3) : Prop := ∀ i, s (i + 1) ≠ s i

/-- The sphere centres `(layer, a, b)` of the packing with stacking `s`. -/
def centres (s : ℤ → ZMod 3) : Set (ℤ × ℤ × ℤ) := {p | ((p.2.1 + p.2.2 : ℤ) : ZMod 3) = s p.1}

/-- Squared distance between two centres (diameter `√3` scale). -/
def dist2 (p q : ℤ × ℤ × ℤ) : ℤ :=
  (p.2.1 - q.2.1) ^ 2 - (p.2.1 - q.2.1) * (p.2.2 - q.2.2) + (p.2.2 - q.2.2) ^ 2 + 2 * (p.1 - q.1) ^ 2

/-- A036559: positive squared distances arising in no Barlow packing. -/
def A036559 : Set ℕ :=
  {D | 1 ≤ D ∧ ¬ ∃ s, IsBarlow s ∧ ∃ p ∈ centres s, ∃ q ∈ centres s, dist2 p q = D}

/-- Conway–Sloane conjecture: the exact description of A036559. -/
theorem main : ∀ D : ℕ, D ∈ A036559 ↔
    ((∃ n : ℕ, D = 4 ^ n ∨ D = 4 ^ n * 7 ∨ D = 4 ^ n * 13 ∨ ∃ k : ℕ, D = 4 ^ n * (16 * k + 10)) ∨
      D ∈ ({2, 5, 14, 23, 38, 230} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a036559
