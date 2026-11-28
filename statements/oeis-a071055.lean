import Mathlib

/-!
# A071055: Number of 0's in n-th row of triangle in A071038.

Source: https://oeis.org/A071055
Credit: @Solfanbtc

A071038 is the triangle of successive states of the elementary cellular automaton "Rule 182"
started from a single 1; row n has length 2n+1 (cells -n..n). Rule 182 = 10110110 in binary:
the new cell is bit (4*left + 2*center + right) of 182. The background stays 0 (000 -> 0).
a(n) is the number of 0 cells among positions -n..n at time n.

Conjectures (FORMULA section), stated together:
1. (R. Stephan, Mar 05 2004) a(n) = b(n+1), with b(0) = 0, b(2n) = b(n),
   b(2n+1) = 2*b(n) + 2 - 2*[n == 0].
2. (F. Hüffner, Jul 26 2019) a(n) = pext(n, n + 1), where pext(x, mask) extracts the bits of x at
   the positions of the set bits of mask (in increasing order) into contiguous low bits.
Both checked numerically for n < 300, together with the data (0, 0, 2, 0, 2, 2, 6, 0, ...).
-/

namespace OMA.S_oeis_a071055

/-- One step of Rule 182 on the neighbourhood (l, c, r). -/
def rule182 (l c r : Bool) : Bool :=
  Nat.testBit 182 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- State of the Rule 182 automaton at time `t`, started from a single 1 at cell 0. -/
def state : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | t + 1, x => rule182 (state t (x - 1)) (state t x) (state t (x + 1))

/-- A071055: number of 0's in row `n` of A071038, i.e. among cells `i - n`, `i < 2n + 1`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter (fun i : ℕ => state n ((i : ℤ) - n) = false)).card

/-- Stephan's auxiliary sequence: b(0) = 0, b(2n) = b(n), b(2n+1) = 2 b(n) + 2 - 2 [n = 0]. -/
def b : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then b ((n + 1) / 2)
    else 2 * b ((n + 1) / 2) + 2 - (if (n + 1) / 2 = 0 then 2 else 0)
decreasing_by all_goals omega

/-- Parallel bits extract: the bits of `x` at the set bits of `mask`, packed into the low bits. -/
def pext (x mask : ℕ) : ℕ :=
  if h : mask = 0 then 0
  else if mask % 2 = 1 then x % 2 + 2 * pext (x / 2) (mask / 2)
  else pext (x / 2) (mask / 2)
decreasing_by all_goals omega

theorem main : (∀ n : ℕ, a n = b (n + 1)) ∧ (∀ n : ℕ, a n = pext n (n + 1)) := by
  sorry

end OMA.S_oeis_a071055
