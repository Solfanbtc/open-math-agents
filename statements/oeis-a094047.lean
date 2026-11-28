import Mathlib

/-!
# A094047: ménage seatings of n couples around a round table, up to rotations

Source: https://oeis.org/A094047
Credit: @Solfanbtc

`a(n)` is the number of seating arrangements of `n` couples around a round table (up to
rotations) so that each person sits between two people of the opposite sex and no couple is
seated together. Offset 1: 0, 0, 2, 12, 312, 9600, ...

Model: the `2n` people are `Fin n × Bool` (couple index, sex); a seating is a bijection from the
seats `Fin (2n)` (in cyclic order; `finRotate (2n) i` is the seat after `i`) to the people. A
seating is valid when any two neighbours have opposite sexes and belong to different couples.
For `n ≥ 1` the `2n` rotations act freely on seatings (all people are distinct), so the number of
seatings up to rotation is the number of valid seatings divided by `2n` (exact division).

The entry records two conjectures of R. J. Mathar (Nov 02 2015), stated here as a conjunction:
1. `a(n) + (-n^2+2n-3) a(n-1) - (n-2)(n^2-3n+5) a(n-2) - 3(n-2)(n-3) a(n-3)
    + (n-2)(n-3)(n-4) a(n-4) = 0`,
2. `(-n+2) a(n) + (n-1)(n^2-3n+3) a(n-1) + (n-2)(n-1)(n^2-3n+3) a(n-2)
    + (n-2)(n-3)(n-1)^2 a(n-3) = 0`.
Index ranges (minimal fix): both recurrences fail at the first index where they would involve
`a(1) = 0` (recurrence 1 at `n = 5`, recurrence 2 at `n = 4`); they hold there if `a(1)` is
replaced by `-1 = A000179(1) * 0!`, the value of the closed formulas `a(n) = A000179(n) (n-1)!`,
which the entry asserts only for `n > 1`. So we state them where all indices are `≥ 2`:
recurrence 1 for `n ≥ 6`, recurrence 2 for `n ≥ 5`.

Sanity check (python): brute force over all seatings gives `a(1..4) = 0, 0, 2, 12` (with exact
division by `2n`); Alekseyev's formula reproduces all 18 listed terms, and with it the two
recurrences hold for `6 ≤ n < 300` and `5 ≤ n < 300` respectively. In Lean, `#eval` of the number
of `Valid` seatings gives 0, 0, 12 for `n = 1, 2, 3` (so `a(3) = 12 / 6 = 2`).
-/

namespace OMA.S_oeis_a094047

/-- A valid ménage seating: neighbours have opposite sexes and are not a couple. -/
def Valid (n : ℕ) (s : Fin (2 * n) ≃ Fin n × Bool) : Prop :=
  ∀ i : Fin (2 * n), (s i).2 ≠ (s (finRotate (2 * n) i)).2 ∧
    (s i).1 ≠ (s (finRotate (2 * n) i)).1

/-- A094047: valid seatings counted up to the `2n` rotations. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {s : Fin (2 * n) ≃ Fin n × Bool // Valid n s} / (2 * n)

/-- Mathar's two conjectured recurrences for A094047. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n →
      let m : ℤ := n;
      a n + (-m ^ 2 + 2 * m - 3) * a (n - 1) - (m - 2) * (m ^ 2 - 3 * m + 5) * a (n - 2)
        - 3 * (m - 2) * (m - 3) * a (n - 3) + (m - 2) * (m - 3) * (m - 4) * a (n - 4) = 0) ∧
    (∀ n : ℕ, 5 ≤ n →
      let m : ℤ := n;
      (-m + 2) * a n + (m - 1) * (m ^ 2 - 3 * m + 3) * a (n - 1)
        + (m - 2) * (m - 1) * (m ^ 2 - 3 * m + 3) * a (n - 2)
        + (m - 2) * (m - 3) * (m - 1) ^ 2 * a (n - 3) = 0) := by
  sorry

end OMA.S_oeis_a094047
