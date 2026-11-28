import Mathlib

/-!
# A092131: Distance from 2^n to the next prime.

Source: https://oeis.org/A092131
Credit: @Solfanbtc

`a(n) = nextprime(2^n) - 2^n` (offset 1), where `nextprime(x)` is the least prime `≥ x`
(PARI convention, which gives `a(1) = 0` since `2` is prime; e.g. `a(13) = 17`,
`2^13 + 17 = 8209`).

A Sierpiński number is an odd `k` such that `k · 2^m + 1` is composite for every `m ≥ 1`
(A076336). No term `a(n)` can be a Sierpiński number.

Conjecture (Jianing Song, May 28 2024): every odd number which is not a Sierpiński number is a
term, i.e. for every odd `k` that is not a Sierpiński number there is `n ≥ 1` with `a(n) = k`
(equivalently, as the entry says: `2^n + 1, 2^n + 3, …, 2^n + (k-2)` are all composite while
`2^n + k` is prime; for `n ≥ 1` every `2^n + j` with `j ≥ 2` even is composite).
-/

namespace OMA.S_oeis_a092131

/-- `a(n) = nextprime(2^n) - 2^n`, with `nextprime(x)` the least prime `≥ x`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (2 ^ n)) - 2 ^ n

/-- `k` is a Sierpiński number: `k` is odd and `k · 2^m + 1` is composite for all `m ≥ 1`. -/
def IsSierpinski (k : ℕ) : Prop :=
  Odd k ∧ ∀ m : ℕ, 1 ≤ m → 1 < k * 2 ^ m + 1 ∧ ¬ (k * 2 ^ m + 1).Prime

/-- Song's conjecture: every odd non-Sierpiński number occurs in A092131. -/
theorem main : ∀ k : ℕ, Odd k → ¬ IsSierpinski k → ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  sorry

end OMA.S_oeis_a092131
