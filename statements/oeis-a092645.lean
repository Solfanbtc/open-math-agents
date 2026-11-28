import Mathlib

/-!
# A092645: Number of consecutive prime runs of just 4 primes congruent to 1 mod 4 below 10^n.

Source: https://oeis.org/A092645
Credit: @Solfanbtc

Label each prime by its residue mod 4. A run of just 4 is a maximal block of exactly 4
consecutive primes `≡ 1 (mod 4)`: the primes `p_i, …, p_{i+3}` are `≡ 1 (mod 4)`, and the
neighbours `p_{i-1}` and `p_{i+4}` are `≡ 3 (mod 4)`. Here `p_j = Nat.nth Nat.Prime j`, so `p_0 = 2`
and `i ≥ 1`. `a(n)` counts the runs whose four primes are below `10^n`. Checked with python3:
this gives 0, 0, 2, 10, 124, 1047, 8756 for `n = 1..7`, matching the data.

Conjecture (C. R. Greathouse IV, 2011): `a(n) ~ 10^n / (64 · log 10 · n)`. `main` states this
as `n → ∞`. (The terms near the upper limit `10^n` do not affect the asymptotics.)
-/

namespace OMA.S_oeis_a092645

open Filter Asymptotics Real

/-- The `j`-th prime, `p 0 = 2`. -/
noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime j

/-- A maximal run of exactly four primes `≡ 1 (mod 4)` starts at index `i`. -/
def RunAt (i : ℕ) : Prop :=
  1 ≤ i ∧ (∀ j < 4, p (i + j) % 4 = 1) ∧ p (i - 1) % 4 = 3 ∧ p (i + 4) % 4 = 3

open Classical in
/-- `a n`: the number of such runs with all four primes below `10^n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter (fun i => RunAt i ∧ p (i + 3) < 10 ^ n)).card

theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop] fun n => (10 : ℝ) ^ n / (64 * log 10 * n) := by
  sorry

end OMA.S_oeis_a092645
