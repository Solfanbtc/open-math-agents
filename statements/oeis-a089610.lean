import Mathlib

/-!
# A089610: Number of primes between n^2 and (n+1/2)^2.

Source: https://oeis.org/A089610
Credit: @Solfanbtc

`a(n)` is the number of primes `p` with `n^2 < p < (n + 1/2)^2 = n^2 + n + 1/4`, i.e. the number
of primes in `[n^2, n^2 + n]` (`n^2` is never prime and `n^2 + n` is even and `> 2` for
`n ≥ 2`; for `n = 1` the count is 1, the prime 2). This is the entry's PARI program
`primepi(n^2+n) - primepi(n^2)`.

Conjecture (Cino Hilliard, %C): after `n = 17`, `a(n) > 1`, i.e. for every `n ≥ 18` there are at
least two primes between `n^2` and `(n+1/2)^2`. (`a(17) = 1`: only 293 lies in `[289, 306]`.)
This is a strengthening of Oppermann's conjecture `a(n) > 0`, which is stated upstream
(`oppermann_conjecture.parts.ii`); it is not implied by it.

The entry's second conjecture (`a(n) < a(n+1)` for all `n ≥ n₁`) is a separate claim and is not
stated here; the data contradicts any such `n₁ ≤ 9997` (e.g. `a(9998) ≥ a(9999)`).
Checked with python3: `a(1..20)` agree with %S, and `a(n) ≥ 2` for all `18 ≤ n ≤ 10000`.
-/

namespace OMA.S_oeis_a089610

/-- A089610: number of primes in `[n^2, n^2 + n]`, i.e. strictly between `n^2` and `(n+1/2)^2`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc (n ^ 2) (n ^ 2 + n)).filter Nat.Prime).card

/-- Hilliard's conjecture: `a(n) > 1` for all `n > 17`. -/
theorem main : ∀ n : ℕ, 17 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a089610
