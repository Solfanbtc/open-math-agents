import Mathlib

/-!
# A088201: p - LQnR(p) where the difference of LQnR is ≤ 0

Source: https://oeis.org/A088201
Credit: @Solfanbtc

`LQnR(p)` (A088196) is the largest number in `[1, p-1]` that is not a quadratic residue modulo the
prime `p`. A088197 is its first-difference sequence over consecutive primes,
`LQnR(prime(n+1)) - LQnR(prime(n))`; A088200 lists the differences that are `≤ 0`, and A088201 the
corresponding distances `q - LQnR(q)` (A088198) at the later prime `q = prime(n+1)`:
`5, 5, 7, 5, 5, 7, 5, 11, …` (a computation reproduces the A088200 and A088201 data with this
alignment; aligning at `prime(n)` does not).

Conjecture (OEIS comment): "The terms are conjectured to be odd primes `> 3` (the primality is
provable)". Stated as: whenever `LQnR(q') ≤ LQnR(q)` for consecutive odd primes `q < q'`, the
distance `q' - LQnR(q')` is a prime `> 3` (hence odd). With Mathlib's 0-indexed
`p j = Nat.nth Nat.Prime j`, odd primes are `p j` with `j ≥ 1`. (Python: holds for all 5506 terms
with `q' < 2·10^6`.)

Not stated: the second conjecture of the entry, "the i-th member of A088200 is `-2` iff `a(i)` is
`5`", is false: for the consecutive primes `7673, 7681`, `LQnR = 7670, 7668` (difference `-2`, the
50th member of A088200) but `a(50) = 7681 - 7668 = 13` (checked by brute force).
-/

namespace OMA.S_oeis_a088201

/-- The `j`-th prime, 0-indexed (`p 0 = 2`). -/
noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime j

open Classical in
/-- `LQnR(q)`: the largest `m ∈ [1, q-1]` that is not a square modulo `q`. -/
noncomputable def LQnR (q : ℕ) : ℕ :=
  ((Finset.Icc 1 (q - 1)).filter fun m : ℕ => ¬ IsSquare ((m : ℕ) : ZMod q)).sup (fun m : ℕ => m)

/-- The terms of A088201 are primes `> 3`. -/
theorem main : ∀ j : ℕ, 1 ≤ j → LQnR (p (j + 1)) ≤ LQnR (p j) →
    (p (j + 1) - LQnR (p (j + 1))).Prime ∧ 3 < p (j + 1) - LQnR (p (j + 1)) := by
  sorry

end OMA.S_oeis_a088201
