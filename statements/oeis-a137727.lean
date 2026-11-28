import Mathlib

/-!
# A137727: Final digit of prime(n)*prime(n+1).

Source: https://oeis.org/A137727
Credit: @Solfanbtc

Claim (entry comment, Charles R Greathouse IV, 2013): "1 and 9 appear 17/66 of the time and 3
and 7 appear 8/33 of the time", read as natural densities: for d = 1 and d = 9 the proportion of
n ≤ N with a(n) = d tends to 17/66, and for d = 3 and d = 7 it tends to 8/33. (The same comment
also notes the elementary fact that a(n) ∈ {1, 3, 7, 9} for n > 3; the four densities add up to 1.)

Conventions: a(n) = (prime(n)·prime(n+1)) mod 10 with prime(1) = 2 (offset 1). In Lean the
primes are `Nat.nth Nat.Prime m` with m = n - 1 starting at 0, so the count over n = 1..N is the
count over m < N. For context: a python count over the primes below 10^8 gives proportions
0.2285, 0.2702, 0.2831, 0.2182 for d = 1, 3, 7, 9, and the Hardy–Littlewood heuristics
(Lemke Oliver–Soundararajan) predict 1/4 for each, so the claim is probably false. It is stated
as conjectured.
-/

namespace OMA.S_oeis_a137727

/-- a(m+1) = final digit of prime(m+1)·prime(m+2), with 0-indexed `Nat.nth Nat.Prime`. -/
noncomputable def a (m : ℕ) : ℕ := (Nat.nth Nat.Prime m * Nat.nth Nat.Prime (m + 1)) % 10

/-- Proportion of n ≤ N with a(n) = d. -/
noncomputable def freq (d N : ℕ) : ℝ := (((Finset.range N).filter fun m => a m = d).card : ℝ) / N

theorem main :
    Filter.Tendsto (freq 1) Filter.atTop (nhds (17 / 66)) ∧
    Filter.Tendsto (freq 9) Filter.atTop (nhds (17 / 66)) ∧
    Filter.Tendsto (freq 3) Filter.atTop (nhds (8 / 33)) ∧
    Filter.Tendsto (freq 7) Filter.atTop (nhds (8 / 33)) := by
  sorry

end OMA.S_oeis_a137727
