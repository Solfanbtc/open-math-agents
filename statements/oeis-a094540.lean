import Mathlib

/-!
# A094540: Last digit of the n-th perfect number.

Source: https://oeis.org/A094540
Credit: @Solfanbtc

`a(n)` (offset 1) is the last decimal digit of the `n`-th perfect number (A000396, in increasing
order: 6, 28, 496, 8128, ...): 6, 8, 6, 8, 6, 6, 8, 8, ... Here `perfect i` is the `(i+1)`-th
perfect number (`Nat.nth Nat.Perfect i`), and `count d n` is the number of 6's or 8's among
`a(1), …, a(n)`.

Conjecture (J. Lowell, 2007): the ratio of 6's to 8's approaches 1.5 as a limit. `main` states
`count 6 n / count 8 n → 3/2` as `n → ∞`. (The conjecture presupposes infinitely many perfect
numbers. An even perfect number `2^(p-1) (2^p - 1)` with `p > 2` ends in 6 if `p ≡ 1 (mod 4)`
and in 8 if `p ≡ 3 (mod 4)`, so the claim is about a bias of the Mersenne prime exponents
mod 4; heuristics would rather suggest a ratio of 1. It is stated as the source
states it.)
-/

namespace OMA.S_oeis_a094540

open Filter Topology

/-- The `(i+1)`-th perfect number. -/
noncomputable def perfect (i : ℕ) : ℕ := Nat.nth Nat.Perfect i

/-- Number of `i < n` such that the `(i+1)`-th perfect number ends in the digit `d`. -/
noncomputable def count (d n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => perfect i % 10 = d)).card

theorem main :
    Tendsto (fun n : ℕ => (count 6 n : ℝ) / (count 8 n : ℝ)) atTop (𝓝 (3 / 2)) := by
  sorry

end OMA.S_oeis_a094540
