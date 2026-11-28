import Mathlib

/-!
# A082477: Number of divisors d of n such that d+1 is also a divisor of n+1.

Source: https://oeis.org/A082477
Credit: @Solfanbtc

`a(n) = #{d : d ∣ n and (d + 1) ∣ (n + 1)}` for `n ≥ 1`. This reproduces the data and the
partial sums `15, 185, 1952, 19852, 199538, 1998538` up to `10^6` quoted in the entry (Python).

Conjecture (Amiram Eldar, Jun 04 2022): the asymptotic mean of the sequence is `2`, i.e.
`(1/N) Σ_{n=1}^{N} a(n) → 2`.

Remark: this seems to follow from an elementary count. `d ∣ n` and `d + 1 ∣ n + 1` means
`n ≡ d (mod d(d+1))` (the g.f. `Σ x^k/(1 - x^(k(k+1)))`, V. Jovovic). So
`Σ_{n ≤ N} a(n) = Σ_{d ≤ N} (⌊(N-d)/(d(d+1))⌋ + 1) = N + N Σ 1/(d(d+1)) + O(√N) = 2N + O(√N)`.
The entry still labels it a conjecture.
-/

namespace OMA.S_oeis_a082477

/-- A082477. -/
def a (n : ℕ) : ℕ := (n.divisors.filter (fun d => (d + 1) ∣ (n + 1))).card

theorem main :
    Filter.Tendsto (fun N : ℕ => ((∑ n ∈ Finset.Icc 1 N, a n : ℕ) : ℝ) / N)
      Filter.atTop (nhds 2) := by
  sorry

end OMA.S_oeis_a082477
