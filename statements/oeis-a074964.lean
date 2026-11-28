import Mathlib

/-!
# A074964: Numbers k such that Max ( sigma(x*y) : 1 <= x <= k, 1 <= y <= k ) = sigma(k^2).

Source: https://oeis.org/A074964 (and https://oeis.org/A066522)
Credit: @Solfanbtc

`k ≥ 1` is a term when `max {σ(xy) : 1 ≤ x, y ≤ k} = σ(k²)`. Since `σ(k²)` is one of the values
(`x = y = k`), this is the same as `σ(xy) ≤ σ(k²)` for all `1 ≤ x, y ≤ k`.
Known terms: 1, 2, 3, 4, 6, 8, 12, 18, 24, 60 (reproduced by a Python search over `k ≤ 130`;
the entry reports no further term below 40000).

A066522: numbers `m` whose divisors `≤ √m` are consecutive, from 1 up to some number `j`,
i.e. `{d ∣ m : d² ≤ m} = {1, ..., j}` for some `j`.

Conjecture (R. Zumkeller, 2011): A074964 is a subsequence of A066522, implying finiteness;
the entry also says (B. Cloitre) the sequence is probably finite. Both are stated: every term of
A074964 is in A066522, and A074964 is finite. (A066522 itself is infinite: it contains every `p`
and `2p` with `p` prime, so finiteness is recorded as its own conjunct.)
-/

namespace OMA.S_oeis_a074964


/-- Membership in A074964. -/
def InA074964 (k : ℕ) : Prop :=
  1 ≤ k ∧ ∀ x ∈ Finset.Icc 1 k, ∀ y ∈ Finset.Icc 1 k,
    ArithmeticFunction.sigma 1 (x * y) ≤ ArithmeticFunction.sigma 1 (k ^ 2)

/-- Membership in A066522: the divisors `d` of `m` with `d² ≤ m` are exactly `1, ..., j`. -/
def InA066522 (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ j : ℕ, (m.divisors.filter (fun d => d * d ≤ m)) = Finset.Icc 1 j

theorem main : (∀ k : ℕ, InA074964 k → InA066522 k) ∧ {k : ℕ | InA074964 k}.Finite := by
  sorry

end OMA.S_oeis_a074964
