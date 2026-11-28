import Mathlib

/-!
# A084569: Partial sums of A084570.

Source: https://oeis.org/A084569
Credit: @Solfanbtc

A084570 is the sequence of partial sums of A084263 (`i + (-1)^i`), so (formula of the entry)
`a(n) = ∑_{k=0..n} ∑_{j=0..k} ∑_{i=0..j} (i + (-1)^i)`, offset 0: `1, 3, 9, 21, 44, ...`.

Conjecture (R. J. Mathar, Mar 08 2025): `a(n)` is the number of perimeter-magic (hollow)
squares of order 3 with magic sum `n + 3`. Each of the 4 edges has 3 elements `≥ 1`, the
square has 8 elements, read counterclockwise as `x 0, ..., x 7` with corners `x 0, x 2, x 4, x 6`
and edges `(x 0, x 1, x 2), (x 2, x 3, x 4), (x 4, x 5, x 6), (x 6, x 7, x 0)`, each summing to
the magic sum. Elements need not be distinct, and squares obtained by rotations (a quarter
turn shifts the reading by 2 places) are counted once; reflections are not identified. Each
element is at most the magic sum, so the search is over `[1, S]^8`. Checked by computer
for `n < 25`; e.g. for magic sum 4 the 3 squares are `11211121`, `11211212`, `12121212`.
-/

namespace OMA.S_oeis_a084569

/-- A084569: `a(n) = ∑_{k ≤ n} ∑_{j ≤ k} ∑_{i ≤ j} (i + (-1)^i)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1),
    ((i : ℤ) + (-1) ^ i)

/-- The perimeter of a 3×3 square read counterclockwise has magic sum `S`. -/
def IsMagic (S : ℕ) (x : Fin 8 → ℕ) : Prop :=
  x 0 + x 1 + x 2 = S ∧ x 2 + x 3 + x 4 = S ∧ x 4 + x 5 + x 6 = S ∧ x 6 + x 7 + x 0 = S

instance (S : ℕ) (x : Fin 8 → ℕ) : Decidable (IsMagic S x) := by
  unfold IsMagic; infer_instance

/-- Perimeter-magic squares of order 3 with elements `≥ 1` and magic sum `S`. -/
def squares (S : ℕ) : Finset (Fin 8 → ℕ) :=
  (Fintype.piFinset fun _ => Finset.Icc 1 S).filter (IsMagic S)

/-- Rotation by `r` quarter turns: the counterclockwise reading shifts by `2 r` places. -/
def rotate (r : ℕ) (x : Fin 8 → ℕ) : Fin 8 → ℕ := fun i => x (Fin.ofNat 8 (i.val + 2 * r))

/-- The set of rotations of a square. -/
def rotations (x : Fin 8 → ℕ) : Finset (Fin 8 → ℕ) := (Finset.range 4).image fun r => rotate r x

/-- Mathar's conjecture: `a(n)` is the number of perimeter-magic squares of order 3 with magic
sum `n + 3`, counted up to rotation. -/
theorem main : ∀ n : ℕ, (((squares (n + 3)).image rotations).card : ℤ) = a n := by
  sorry

end OMA.S_oeis_a084569
