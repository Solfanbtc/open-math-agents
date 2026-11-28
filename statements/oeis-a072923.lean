import Mathlib

/-!
# A072923: Number of primes of the form floor((1 + 1/k)^n), 1 ≤ k ≤ n

Source: https://oeis.org/A072923
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of `k`, `1 ≤ k ≤ n`, for which `⌊(1 + 1/k)^n⌋` is prime (counted
with multiplicity in `k`: for `n = 15`, `k = 7, 8, 11, 12, 13, 14, 15` give `7, 5, 3, 3, 3, 2, 2`,
so `a(15) = 7`): `1, 1, 2, 3, 3, 5, 5, 4, …` (exact integer arithmetic reproduces the first 20 data
terms). Note `⌊(1 + 1/k)^n⌋ = ⌊(k+1)^n / k^n⌋`.

Conjecture (Benoit Cloitre, Aug 11 2002, OEIS formula): `a(n)` is asymptotic to `C n` with
`C = 0.47…`. Stated as: there is `C` with decimal expansion beginning `0.47` (`0.47 ≤ C < 0.48`) and
`a(n)/n → C` (`a(n) ~ C n` with `C > 0`).

Remark (evidence against the stated value, not in the entry): with `k = t n`,
`(1 + 1/k)^n → e^(1/t)`, which suggests `a(n)/n → ∑_p |{t ∈ (0, 1] : ⌊e^(1/t)⌋ = p}|
= (1 - 1/log 3) + ∑_{p ≥ 3} (1/log p - 1/log(p+1)) ≈ 0.461`; numerically `a(n)/n ≈ 0.459` at
`n = 5000` and `20000` (counting only prime values `≤ 3·10^6`, which omits about `0.002`). So the
constant seems to be `0.46…` rather than `0.47…`. The conjecture is stated faithfully as the source
states it.
-/

namespace OMA.S_oeis_a072923

/-- A072923: the number of `k ≤ n` with `⌊(k+1)^n / k^n⌋` prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k => ((k + 1) ^ n / k ^ n).Prime).card

/-- Cloitre's conjecture: `a(n) ~ C n` with `C = 0.47…`. -/
theorem main : ∃ C : ℝ, 0.47 ≤ C ∧ C < 0.48 ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop (nhds C) := by
  sorry

end OMA.S_oeis_a072923
