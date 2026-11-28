import Mathlib

/-!
# A085152: All prime factors of n and n+1 are ≤ 5

Source: https://oeis.org/A085152
Credit: @Solfanbtc

A085152: the numbers `n ≥ 1` such that all prime factors of `n` and `n + 1` are `≤ 5`
(equivalently `n(n+1)` is 5-smooth): `1, 2, 3, 4, 5, 8, 9, 15, 24, 80` (keyword `fini, full`).
The entry relates this to the abc conjecture (which would bound such pairs, D. Rusin).

Status: KNOWN. "This sequence is complete by a theorem of Stormer" (T. D. Noe, OEIS comment):
Størmer's theorem on consecutive smooth numbers shows that these ten values are all. Stated
faithfully as: for `n ≥ 1`, all prime factors of `n` and of `n + 1` are `≤ 5` iff `n` is one of the
ten listed terms.
-/

namespace OMA.S_oeis_a085152

/-- `n` is 5-smooth: every prime factor of `n` is at most `5`. -/
def Smooth5 (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ≤ 5

/-- The ten terms are all `n ≥ 1` with `n` and `n + 1` both 5-smooth (Størmer). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (Smooth5 n ∧ Smooth5 (n + 1) ↔ n ∈ ({1, 2, 3, 4, 5, 8, 9, 15, 24, 80} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a085152
