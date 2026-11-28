import Mathlib

/-!
# A051470: Pólya's conjecture that the summatory Liouville function is ≤ 0 for m ≥ 2 (refuted)

Source: https://oeis.org/A051470
Credit: @Solfanbtc

A051470 (offset 1): `a(n)` is the least `m` such that `L(m) = Sum_{k=1..m} λ(k) = n`, where
`λ(k) = (-1)^Ω(k)` is Liouville's function (`Ω` counts prime factors with multiplicity).
Data 1, 906150258, 906150259, 906150260, …

The entry: "It was once conjectured that the sum of Liouville's function was never > 0 except
for the first term." This is Pólya's conjecture: `L(m) ≤ 0` for all `m ≥ 2`.

Status: false. Haselgrove (1958) disproved it; the least counterexample is `m = 906150257`
(Tanaka, 1980), where `L(m) = 1`; consistently with the data, `a(2) = 906150258` is the first `m`
with `L(m) = 2`. `main` states the conjecture as posed, so that its refutation is a target
(`OMA.disproof`).
-/

namespace OMA.S_oeis_a051470

open ArithmeticFunction

/-- The summatory Liouville function `L(m) = Sum_{k=1..m} (-1)^Ω(k)`. -/
def L (m : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (cardFactors k)

/-- Pólya's (refuted) conjecture: `L(m) ≤ 0` for every `m ≥ 2`. -/
theorem main : ∀ m : ℕ, 2 ≤ m → L m ≤ 0 := by
  sorry

end OMA.S_oeis_a051470
