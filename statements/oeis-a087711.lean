import Mathlib

/-!
# A087711: a(n) = smallest number k such that both k-n and k+n are primes.

Source: https://oeis.org/A087711
Credit: @Solfanbtc

Conjecture (J. Kholdi and F. Firoozbakht, 2014, in the entry): for every positive integer `n`,
`a(n) = b(n) = c(n) = d(n)`, where (over `m > n`)
* `b(n)` is the smallest `m` with `φ(m - n) + σ(m + n) = 2m`,
* `c(n)` is the smallest `m` with `φ(m + n) + σ(m - n) = 2m`,
* `d(n)` is the smallest `m` with `φ(m - n) + σ(m + n) = φ(m + n) + σ(m - n)`.
The comment writes "`= 2n`" for `b` and `c`. This is a typo for `2m`: the same comment restates
the conjecture as "`a(n) < A244446(n)`, `a(n) < A244447(n)`", and those entries use `2*m`. Also,
`m = a(n)` (with `m ∓ n` prime) gives `φ(m-n) + σ(m+n) = (m-n-1) + (m+n+1) = 2m`. So `main` uses
`2m`. Here `φ` is `Nat.totient` and `σ` is `σ 1`.
Checked with python3: `a(n) = b(n) = c(n) = d(n)` for `1 ≤ n < 400`.
-/

namespace OMA.S_oeis_a087711

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `a n`: the least `k` with `k - n` and `k + n` prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | n < k ∧ (k - n).Prime ∧ (k + n).Prime}

/-- `b n`: the least `m > n` with `φ(m - n) + σ(m + n) = 2m`. -/
noncomputable def b (n : ℕ) : ℕ :=
  sInf {m | n < m ∧ Nat.totient (m - n) + σ 1 (m + n) = 2 * m}

/-- `c n`: the least `m > n` with `φ(m + n) + σ(m - n) = 2m`. -/
noncomputable def c (n : ℕ) : ℕ :=
  sInf {m | n < m ∧ Nat.totient (m + n) + σ 1 (m - n) = 2 * m}

/-- `d n`: the least `m > n` with `φ(m - n) + σ(m + n) = φ(m + n) + σ(m - n)`. -/
noncomputable def d (n : ℕ) : ℕ :=
  sInf {m | n < m ∧ Nat.totient (m - n) + σ 1 (m + n) = Nat.totient (m + n) + σ 1 (m - n)}

theorem main : ∀ n : ℕ, 1 ≤ n → a n = b n ∧ a n = c n ∧ a n = d n := by
  sorry

end OMA.S_oeis_a087711
