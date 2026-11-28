import Mathlib

/-!
# A118201: Smallest difference such that both difference and number do not occur previously.

Source: https://oeis.org/A118201
Credit: @Solfanbtc

Definition (the entry's %F line and Maple program): `a(0) = 0`, and `a(n+1) = a(n) - d` or
`a(n) + d`, where `a(n+1)` must be positive and must not have occurred previously in the sequence;
`d` is the smallest positive integer that is not an earlier difference `|a(m+1) - a(m)|`
(`m < n`) for which this is possible; if both `a(n) - d` and `a(n) + d` are admissible, choose
`a(n) - d`. Data: `0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, ...` (offset 0).

Conjecture (Franklin T. Adams-Watters, in the entry): every nonnegative integer occurs in this
sequence. (Through `n = 20000` the smallest missing number is 139.)

Conventions:
* `state n = (values, diffs)`: the values `a(n), ..., a(0)` (newest first) and the differences
  used so far. The new difference is searched in `0 .. S + 1` where `S` is the sum of all values
  and differences so far: `d = S + 1` is always admissible (it exceeds every used difference and
  `a(n) + d` exceeds every value), so this range contains the smallest admissible `d`.
* A python3 mirror of this definition reproduces the 69 data terms, and the Lean kernel checks
  (`decide`) that `a 0, ..., a 14` are `0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9`.
-/

namespace OMA.S_oeis_a118201

/-- `d` is an admissible difference after the history `(vs, ds)` with current value `cur`. -/
def admissible (vs ds : List ℕ) (cur d : ℕ) : Bool :=
  0 < d && !(ds.contains d) && ((d < cur && !(vs.contains (cur - d))) || !(vs.contains (cur + d)))

/-- One step: from `(values (newest first), used differences)` to the next state. -/
def step (s : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let vs := s.1
  let ds := s.2
  let cur := vs.headD 0
  let d := ((List.range (vs.sum + ds.sum + 2)).find? (admissible vs ds cur)).getD 0
  let v := if d < cur && !(vs.contains (cur - d)) then cur - d else cur + d
  (v :: vs, d :: ds)

/-- The state after `n` steps, starting from `a(0) = 0` with no differences used. -/
def state (n : ℕ) : List ℕ × List ℕ := step^[n] ([0], [])

/-- `a n = A118201(n)`. -/
def a (n : ℕ) : ℕ := (state n).1.headD 0

/-- Conjecture: every nonnegative integer occurs in A118201. -/
theorem main : ∀ m : ℕ, ∃ n : ℕ, a n = m := by
  sorry

end OMA.S_oeis_a118201
