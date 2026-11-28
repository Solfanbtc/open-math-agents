import Mathlib

/-!
# A007950: the binary sieve contains infinitely many primes (and composites)

Source: https://oeis.org/A007950
Credit: @Solfanbtc

A007950, the binary sieve (Smarandache 2-ary sieve): from the positive integers
`1, 2, 3, …`, delete every 2nd number, then from the remaining ones every 4th, then every 8th,
and so on (at stage `k` delete every `2^k`-th of the remaining numbers, counting from 1).
Data 1, 3, 5, 9, 11, 13, 17, 21, 25, …

Conjectures (C. T. Le, in the entry): "there are infinitely many primes that belong to this
sequence; also infinitely many composite numbers." The composite half is settled in the entry
(F. T. Adams-Watters: the sequence has positive density A048651 while the primes have density
zero); the prime half is open. `main` states both, as in the source.

Membership. Let `pos_0(x) = x` be the position of `x` among the positive integers and
`pos_k(x)` its position among the numbers left after stage `k`. At stage `k + 1`, `x` (if still
present) is deleted iff `2^(k+1) ∣ pos_k(x)`; otherwise `floor(pos_k(x)/2^(k+1))` earlier numbers
were deleted, so `pos_{k+1}(x) = pos_k(x) - floor(pos_k(x)/2^(k+1))`. Hence `x` is a term iff
`x ≥ 1` and `2^(k+1) ∤ pos_k(x)` for every `k`. Checked with python3: this reproduces the 61
listed terms (and there are 10318 prime terms below `2·10^5`).
-/

namespace OMA.S_oeis_a007950

/-- `pos x k`: the position of `x` after `k` stages of the sieve (as long as it survives). -/
def pos (x : ℕ) : ℕ → ℕ
  | 0 => x
  | k + 1 => pos x k - pos x k / 2 ^ (k + 1)

/-- `x` survives every stage of the binary sieve, i.e. `x` is a term of A007950. -/
def InSieve (x : ℕ) : Prop := 1 ≤ x ∧ ∀ k : ℕ, ¬ 2 ^ (k + 1) ∣ pos x k

/-- Le's conjectures: infinitely many primes and infinitely many composite numbers survive the
binary sieve. -/
theorem main : {p : ℕ | p.Prime ∧ InSieve p}.Infinite ∧
    {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ InSieve n}.Infinite := by
  sorry

end OMA.S_oeis_a007950
