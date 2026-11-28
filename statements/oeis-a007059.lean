import Mathlib

/-!
# A007059: Number of balanced ordered trees with n nodes.

Source: https://oeis.org/A007059
Credit: @Solfanbtc

Conjecture (John W. Layman, Dec 18 2001, listed in the entry): for `n > 0`, `a(n+1)` is the
number of "numbral" divisors of `(4^n - 1)/3 = A002450(n)`. (The entry adds that it follows from
Proposition 2.3 of Frosini and Rinaldi.)

Numbral arithmetic (A048888, Marc LeBrun): addition is bitwise OR and multiplication is
shift-and-OR, so that `[3] * [3] = [7]`. `[d]` divides `[N]` when `[d] * [e] = [N]` for some `[e]`;
for example the six divisors of `[14]` are `[1], [2], [3], [6], [7], [14]`.

Conventions:
- The numbral product `[d] * [e]` has bit `k` set iff `k = i + j` for some set bit `i` of `d` and
  set bit `j` of `e` (the OR over the set bits `j` of `e` of `d` shifted left by `j`). Numbral
  divisors are counted as a set of natural numbers, with `Set.ncard`; there are finitely many,
  since a divisor `d` of `[N]` satisfies `d ≤ N`.
- `a` is defined through the characterization in the entry (Joerg Arndt): for `n ≥ 1`, `a(n)` is the
  number of compositions of `n` in which every part after the first is smaller than the first
  part. This is checked against the listed terms `a(1..15)`; the value at `n = 0` (where the
  entry has `a(0) = 0`) is never used below, since only `a(n+1)` with `n ≥ 1` appears.
- Checked numerically for `1 ≤ n ≤ 7`: `a(n+1)` = 1, 2, 3, 5, 8, 14, 24 equals the number of
  numbral divisors of `(4^n - 1)/3` under this definition (and the divisors of `[14]` are the six
  listed above).
-/

namespace OMA.S_oeis_a007059

/-- A007059 for `n ≥ 1`: compositions of `n` whose later parts are all smaller than the first. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Composition n =>
    ∀ k ∈ c.blocks.tail, k < c.blocks.headI)).card

/-- `[d] * [e] = [N]` in numbral arithmetic: bit `k` of `N` is set iff `k = i + j` with bit `i`
of `d` and bit `j` of `e` set. -/
def NumbralMulEq (d e N : ℕ) : Prop :=
  ∀ k : ℕ, N.testBit k = true ↔ ∃ i j : ℕ, i + j = k ∧ d.testBit i = true ∧ e.testBit j = true

/-- `[d]` is a numbral divisor of `[N]`. -/
def NumbralDvd (d N : ℕ) : Prop := ∃ e : ℕ, NumbralMulEq d e N

/-- Layman's conjecture: for `n > 0`, `a(n+1)` is the number of numbral divisors of
`(4^n - 1)/3`. -/
theorem main : ∀ n : ℕ, 0 < n →
    a (n + 1) = {d : ℕ | NumbralDvd d ((4 ^ n - 1) / 3)}.ncard := by
  sorry

end OMA.S_oeis_a007059
