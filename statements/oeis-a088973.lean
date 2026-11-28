import Mathlib

/-!
# A088973: Number of twin prime pairs between consecutive prime-indexed primes of order 4. The bounds are included in the calculation.

Source: https://oeis.org/A088973
Credit: @Solfanbtc

`prime k` is the `k`-th prime (`prime 1 = 2`). `PIPS4(x) = prime(prime(prime(prime(prime x))))`
(A049203; five applications, as in the entry's formula: `PIPS4(1) = 31`, `PIPS4(2) = 127`).
`a(n)` counts the twin prime pairs `(p, p + 2)` lying entirely in `[PIPS4(n), PIPS4(n+1)]`
(bounds included). For example `a(1) = 5`: (41,43), (59,61), (71,73), (101,103), (107,109).
Checked with python3: `a(1) = 5`, `a(2) = 20`.

Conjecture (C. Hilliard, 2003): the interval `[PIPS4(n), PIPS4(n+1)]` always contains at least one
twin prime pair. (This implies the twin prime conjecture.) `main` states it for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a088973

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- Prime-indexed primes of order 4: `prime` applied five times. -/
noncomputable def PIPS4 (x : ℕ) : ℕ := prime (prime (prime (prime (prime x))))

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ PIPS4 n ≤ p ∧ p + 2 ≤ PIPS4 (n + 1) := by
  sorry

end OMA.S_oeis_a088973
