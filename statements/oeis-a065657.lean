import Mathlib

/-!
# A065657: Numbers m that minimize | k / EulerPhi(k) - golden ratio phi | when k runs over all the numbers with the same number of digits as m.

Source: https://oeis.org/A065657
Credit: @Solfanbtc

Conjecture (OEIS A065657): the listed terms have this property: for r = 1, ..., 5, all r-digit
terms share the same set of prime factors (e.g. the three 3-digit terms 117, 351, 507 have prime
factors 3 and 13); furthermore all listed terms are multiples of 3. "I conjecture that these
properties hold in general": `main` states, for every number of digits r >= 1,
1. any two r-digit terms have the same set of prime factors;
2. every term is a multiple of 3.

Conventions: m has r decimal digits iff 10^(r-1) <= m < 10^r; m is a term (an r-digit minimizer)
iff |m/phi(m) - golden ratio| <= |k/phi(k) - golden ratio| for every r-digit k (phi = Euler's
totient, `Nat.totient`; golden ratio = `Real.goldenRatio`). The set of prime factors is
`Nat.primeFactors`. Checked numerically for r <= 6: the minimizers are 3, 9; 39; 117, 351, 507;
3417; 10251, 30753, 58089, 92259; 656121, matching the data, and both properties hold.
(The entry's further remark, whether |n/phi(n) - golden ratio| can be made arbitrarily small, is
posed only as a question and is not stated here.)
-/

namespace OMA.S_oeis_a065657

/-- `m` minimizes `|k/φ(k) - golden ratio|` among the `r`-digit numbers `k`. -/
def IsTerm (r m : ℕ) : Prop :=
  10 ^ (r - 1) ≤ m ∧ m < 10 ^ r ∧
    ∀ k : ℕ, 10 ^ (r - 1) ≤ k → k < 10 ^ r →
      |(m : ℝ) / (Nat.totient m : ℝ) - Real.goldenRatio| ≤
        |(k : ℝ) / (Nat.totient k : ℝ) - Real.goldenRatio|

theorem main : ∀ r : ℕ, 1 ≤ r →
    (∀ m m' : ℕ, IsTerm r m → IsTerm r m' → m.primeFactors = m'.primeFactors) ∧
    (∀ m : ℕ, IsTerm r m → 3 ∣ m) := by
  sorry

end OMA.S_oeis_a065657
