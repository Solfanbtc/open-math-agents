import Mathlib

/-!
# A085910: a(n) = smallest prime(k) not equal to prime(n) and not included earlier, such that A001223(k) = A001223(n); i.e., prime(k+1) - prime(k) = prime(n+1) - prime(n); or 0 is no such prime exists.

Source: https://oeis.org/A085910
Credit: @Solfanbtc

`prime(k)` is the `k`-th prime (`prime(1) = 2`) and `g(k) = prime(k+1) - prime(k)` (A001223).
Offset 1: `a(n)` is the smallest `prime(k)` with `k ≠ n`, `g(k) = g(n)` and `prime(k)` not
among `a(1), ..., a(n-1)`; `0` if there is none (`sInf ∅ = 0`; so `a(1) = 0`, as `g(1) = 1`
is the only odd gap). We checked by computer that this reproduces all 60 terms of %S, %T, %U.

Conjecture (Amarnath Murthy, 2003): for `n > 1`, `a(n)` is a rearrangement of the odd primes,
i.e. `n ↦ a(n)` is a bijection from `{n | n ≥ 2}` onto the odd primes.
-/

namespace OMA.S_oeis_a085910

/-- `prime(k)`, the `k`-th prime (`prime 1 = 2`). -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- `g(k) = prime(k+1) - prime(k)`. -/
noncomputable def g (k : ℕ) : ℕ := prime (k + 1) - prime k

/-- The term `a(n)` given the list `used` of the earlier terms. -/
noncomputable def next (n : ℕ) (used : List ℕ) : ℕ :=
  sInf {q : ℕ | ∃ k : ℕ, 1 ≤ k ∧ k ≠ n ∧ q = prime k ∧ g k = g n ∧ q ∉ used}

/-- `terms n = [a(1), ..., a(n)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | n + 1 => terms n ++ [next (n + 1) (terms n)]

/-- `a(n)`, offset 1. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

/-- Murthy's conjecture: `(a(n))_{n ≥ 2}` is a rearrangement of the odd primes. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → (a n).Prime ∧ a n ≠ 2) ∧
    (∀ m n : ℕ, 2 ≤ m → 2 ≤ n → a m = a n → m = n) ∧
    (∀ q : ℕ, q.Prime → q ≠ 2 → ∃ n : ℕ, 2 ≤ n ∧ a n = q) := by
  sorry

end OMA.S_oeis_a085910
