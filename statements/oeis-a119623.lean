import Mathlib

/-!
# A119623: a prime value of s2 at a composite n is taken exactly twice

Source: https://oeis.org/A119623 (with https://oeis.org/A119616)
A119616: `s2(n) = ∑_{u ∣ n, v ∣ n, u < v} u v`, the second elementary symmetric function of the
divisors of `n` (0, 2, 3, 14, 5, 47, 7, 70, ...); `s2(p) = p` for `p` prime. A119623 lists the
composite `n` with `s2(n)` prime: 6, 10, 14, 26, 34, 62, ...
The entry: "Terms in A119616 are always prime if n is prime p and s2(p)=p, hence it is
interesting to find composite numbers for which s2 is also prime. ... Otherwise the sequence s2
gives numbers which appear in A119616 at least twice (and conjecture is that exactly twice)."

That is, for a composite `n` with `s2(n) = q` prime, `q` is taken by `s2` at least twice (at `n`
and at `q`, since `s2(q) = q`), and the conjecture is that it is taken exactly twice. We state:
for every composite `n` with `s2(n)` prime, exactly two `m ≥ 1` have `s2(m) = s2(n)`.
(The set is finite: `s2(m) ≥ 1·m` for `m ≥ 2`, so `m ≤ s2(n)`.)
Checked with python3 (sieve of `σ_1`, `σ_2`, with `s2 = (σ_1^2 - σ_2)/2`): the 45 listed terms,
and the conjecture for all 56 composite `n ≤ 5000` with `s2(n)` prime and `≤ 4·10^6`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a119623

/-- A119616: the second elementary symmetric function of the divisors of `n`. -/
def s2 (n : ℕ) : ℕ :=
  ∑ p ∈ (n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2), p.1 * p.2

theorem main : ∀ n : ℕ, 1 < n → ¬ n.Prime → (s2 n).Prime →
    {m : ℕ | 1 ≤ m ∧ s2 m = s2 n}.ncard = 2 := by
  sorry

end OMA.S_oeis_a119623
