import Mathlib

/-!
# A094470: Numbers k such that phi(k) | sigma_18(k).

Source: https://oeis.org/A094470
Credit: @Solfanbtc

`σ_e(k)` is the sum of the `e`-th powers of the divisors of `k` (A013966 for `e = 18`).
The entry's comment (Labos Elemer, May 25 2004): *Conjecture: analogous sequences with any
`4j+2` exponent instead of 18, includes all terms of A015759 [with exponent = 2].*
That is: for every `j ≥ 0`, every `k` with `φ(k) ∣ σ_2(k)` (A015759) also satisfies
`φ(k) ∣ σ_{4j+2}(k)`. (A015759 carries the same claim, with a sketch of proof.)

Remark (computer check, not part of the source): the conjecture appears to be false.
`k = 5952812500 = 2^2 * 5^7 * 43 * 443`, a listed term of A015759, has
`φ(k) = 2320500000 ∣ σ_2(k)`, but `σ_6(k) ≡ σ_18(k) ≡ 663000000 (mod φ(k))`, i.e. it fails
for `j = 1` and for `j = 4` (exponent 18 itself). All smaller listed terms of A015759 satisfy
the claim for `j < 300`. The statement is kept faithful; a disproof is welcome.
-/

namespace OMA.S_oeis_a094470

/-- Conjecture of A094470: if `φ(k) ∣ σ_2(k)`, then `φ(k) ∣ σ_{4j+2}(k)` for every `j`. -/
theorem main :
    ∀ k : ℕ, 0 < k → k.totient ∣ ArithmeticFunction.sigma 2 k →
      ∀ j : ℕ, k.totient ∣ ArithmeticFunction.sigma (4 * j + 2) k := by
  sorry

end OMA.S_oeis_a094470
