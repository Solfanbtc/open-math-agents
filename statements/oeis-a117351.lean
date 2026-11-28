import Mathlib

/-!
# A117351: Where n appears in A082224, provided A082224 is read as a sequence rather than as an array.

Source: https://oeis.org/A117351
Credit: @Solfanbtc

Conjecture (entry comment): the sequence is a permutation of the positive integers.

Definitions.
* A082224 is a square array A(i, j) (i, j ≥ 1) filled along antidiagonals i + j = s = 2, 3, ...,
  alternately upwards and downwards, in the order of the PARI program of both entries: for odd
  s the cells (i, s-i), i = 1..s-1; for even s the cells (s-i, i), i = 1..s-1. Each A(i, j) is
  the least positive integer not used before such that (1) if j > 1, the j-th partial sum of
  row i, A(i,1) + ... + A(i,j), is prime, and (2) if i > 1, the i-th partial sum of column j,
  A(1,j) + ... + A(i,j), is composite (not prime; it is ≥ 2). A(1,1) = 1 comes out of the rule.
  Read in filling order this gives the sequence A082224(1), A082224(2), ...
* A117351(n) is the position k of n in that sequence.
* "A117351 is a permutation of the positive integers" means: the construction never gets
  stuck (every A082224(k) is a positive integer; if no candidate existed the value would be
  `sInf ∅ = 0`), and every positive integer n occurs in A082224 (then A117351(n) is defined;
  injectivity and surjectivity of A117351 are then automatic, since A082224 never repeats a
  value and every position holds a value).
python3 reproduces the 69 data terms of A082224 and the 66 data terms of A117351.
-/

namespace OMA.S_oeis_a117351

/-- The cells of antidiagonals `2, ..., M` in filling order (row, column). -/
def cells (M : ℕ) : List (ℕ × ℕ) :=
  (List.range' 2 (M - 1)).flatMap fun s =>
    (List.range' 1 (s - 1)).map fun i => if s % 2 = 1 then (i, s - i) else (s - i, i)

/-- The `k`-th cell to be filled (k ≥ 1). -/
def cellAt (k : ℕ) : ℕ × ℕ := (cells (k + 2)).getD (k - 1) (0, 0)

/-- The first `k` filled cells with their values: (row, column, value). -/
noncomputable def filled : ℕ → List (ℕ × ℕ × ℕ)
  | 0 => []
  | k + 1 =>
    let L := filled k
    let rc := cellAt (k + 1)
    let p1 := ((L.filter fun t => t.1 = rc.1 ∧ t.2.1 < rc.2).map fun t => t.2.2).sum
    let p2 := ((L.filter fun t => t.2.1 = rc.2 ∧ t.1 < rc.1).map fun t => t.2.2).sum
    L ++ [(rc.1, rc.2, sInf {n : ℕ | 0 < n ∧ n ∉ L.map (fun t => t.2.2) ∧
      (1 < rc.2 → (p1 + n).Prime) ∧ (1 < rc.1 → ¬ (p2 + n).Prime)})]

/-- A082224(k), offset 1. -/
noncomputable def A082224 (k : ℕ) : ℕ := ((filled k).getD (k - 1) (0, 0, 0)).2.2

theorem main :
    (∀ k : ℕ, 1 ≤ k → 0 < A082224 k) ∧ (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ A082224 k = n) := by
  sorry

end OMA.S_oeis_a117351
