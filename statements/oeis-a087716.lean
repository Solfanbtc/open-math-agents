import Mathlib

/-!
# A087716: Base-2 pseudoprimes (see A001567) of the form j*p(i)# - p(k) or j*p(i)# + p(k), p(i) and p(k) primes with p(i) < p(k) < p(i+1)^2 and 0 < j < p(i+1).

Source: https://oeis.org/A087716
Credit: @Solfanbtc

A base-2 pseudoprime (A001567) is a composite `n` with `2^(n-1) ≡ 1 (mod n)`. `p(i)` is the
`i`-th prime and `p#` the primorial (product of the primes `≤ p`, Mathlib's `primorial`). A term
is a base-2 pseudoprime `n` with `n = j·p(i)# - r` or `n = j·p(i)# + r` for some `i ≥ 1`, prime `r`
with `p(i) < r < p(i+1)^2`, and `0 < j < p(i+1)` (the subtraction is taken in `ℤ`, so `n` is the
positive integer `j·p(i)# - r`). Examples from the entry: `341 = 2·7# - 79`,
`1387 = 7·7# - 83`, `2047 = 10·7# - 53`, `4681 = 2·11# + 61`, `13747 = 6·11# - 113`.
(`2701 = 13·7# - 29` is not a term: `j = 13 ≥ p(i+1) = 11`.)

Conjecture (in the entry): the sequence has only these 5 terms (checked there for all `i ≤ 150`;
rechecked here in Python for `p(i) ≤ 60`). Stated as: the set of terms is exactly
`{341, 1387, 2047, 4681, 13747}`. With `0`-indexed `Nat.nth`, `p(i) = Nat.nth Nat.Prime i'` for
`i' = i - 1` and `p(i+1) = Nat.nth Nat.Prime (i' + 1)`.
-/

namespace OMA.S_oeis_a087716

/-- `n` is a base-2 Fermat pseudoprime (A001567). -/
def Psp2 (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧ 2 ^ (n - 1) % n = 1

/-- `n` has the required form, with `p(i) = Nat.nth Nat.Prime i'`. -/
def HasForm (n : ℕ) : Prop :=
  ∃ i' j r : ℕ, r.Prime ∧ Nat.nth Nat.Prime i' < r ∧ r < (Nat.nth Nat.Prime (i' + 1)) ^ 2 ∧
    0 < j ∧ j < Nat.nth Nat.Prime (i' + 1) ∧
    ((n : ℤ) = j * primorial (Nat.nth Nat.Prime i') - r ∨
      (n : ℤ) = j * primorial (Nat.nth Nat.Prime i') + r)

theorem main : {n : ℕ | Psp2 n ∧ HasForm n} = {341, 1387, 2047, 4681, 13747} := by
  sorry

end OMA.S_oeis_a087716
