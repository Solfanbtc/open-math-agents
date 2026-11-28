import Mathlib

/-!
# A063869: Least k such that sigma(k) = m^n for some m > 1

Source: https://oeis.org/A063869
Credit: @Solfanbtc

`a(n)` (offset 1) is the least `k` such that `σ(k) = m^n` for some `m > 1`:
`2, 3, 7, 217, 21, 2667, 93, …` (e.g. `σ(2752491) = σ(3 · 7 · 131071) = 4^11`).

Question (Labos Elemer, OEIS comment): "For `n = 2` to `20`, `σ(a(n)) = m^n` with `m = 2` or
`m = 4`. Computed terms are products of Mersenne primes (A000668). Is this true for larger `n`?"
Stated in its expected form: for every `n ≥ 2`, every prime factor of `a(n)` is a Mersenne prime
`2^q - 1` (i.e. `a(n)` is a product of Mersenne primes; `a(1) = 2` is not, which is why the
comment starts at `n = 2`). Since it is not known that a `k` exists for every `n`, the claim is
stated for the least such `k` whenever one exists (`IsLeast`). (Python: the data terms for
`2 ≤ n ≤ 22` are products of Mersenne primes.)
-/

namespace OMA.S_oeis_a063869

open ArithmeticFunction

/-- `k ≥ 1` with `σ(k) = m^n` for some `m > 1`. -/
def Good (n k : ℕ) : Prop := 1 ≤ k ∧ ∃ m : ℕ, 1 < m ∧ sigma 1 k = m ^ n

/-- For `n ≥ 2`, the least `k` with `σ(k)` a perfect `n`-th power `> 1` is a product of Mersenne
primes. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, IsLeast {k | Good n k} k →
    ∀ p : ℕ, p.Prime → p ∣ k → ∃ q : ℕ, p = 2 ^ q - 1 := by
  sorry

end OMA.S_oeis_a063869
