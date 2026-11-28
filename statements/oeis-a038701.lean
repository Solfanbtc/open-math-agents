import Mathlib

/-!
# A038701: Prime powers q for which f(g(m(q))) = m(q), where f = A051703, g = A008475 and m = A003418.

Source: https://oeis.org/A038701
Credit: @Solfanbtc

With (as defined in the entry):
* `g(x) = ∑ p_j^{k_j}` for `x = ∏ p_j^{k_j}` (A008475; `g(1) = 0`);
* `f(n) = max {x : g(x) = n}` (A051703);
* `m(n) = lcm(1, 2, ..., n)` (A003418),
A038701 lists the prime powers `q` with `f(g(m(q))) = m(q)`:
`2, 3, 4, 5, 7, 8, 9, 11, 13, 16, ..., 103, 107, 109, 113` (no other terms below 409, per
Max Alekseyev). Since `m(q)` itself has `g`-value `g(m(q))`, always `f(g(m(q))) ≥ m(q)`.

Conjecture (Vladeta Jovovic, in the entry): the sequence is finite, i.e. `f(g(m(q))) > m(q)` for
all sufficiently large prime powers `q`. Stated as: the set of prime powers `q` with
`f(g(m(q))) = m(q)` is finite.

A python3 check: with these definitions (computing `f` by maximizing products over sums of
powers of distinct primes) the prime powers `q < 140` in the set are exactly the data terms.

Conventions: `f(n)` is `sSup {x ≥ 1 | g(x) = n}` (a finite set: every prime-power factor of such
`x` is at most `n`).
-/

namespace OMA.S_oeis_a038701

/-- `g = A008475`: the sum of the prime-power factors `p^{k}` of `x` (`g(1) = 0`). -/
def g (x : ℕ) : ℕ := ∑ p ∈ x.primeFactors, p ^ (x.factorization p)

/-- `f = A051703`: `f(n) = max {x : g(x) = n}`. -/
noncomputable def f (n : ℕ) : ℕ := sSup {x : ℕ | 1 ≤ x ∧ g x = n}

/-- `m = A003418`: `m(n) = lcm(1, ..., n)`. -/
def m (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- Jovovic's conjecture: only finitely many prime powers `q` satisfy `f(g(m(q))) = m(q)`. -/
theorem main : {q : ℕ | IsPrimePow q ∧ f (g (m q)) = m q}.Finite := by
  sorry

end OMA.S_oeis_a038701
