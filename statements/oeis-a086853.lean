import Mathlib

/-!
# A086853: Number of permutations of length n with exactly 2 rising or falling successions.

Source: https://oeis.org/A086853
Credit: @Solfanbtc

`a(n)` (offset 0) counts the permutations `σ` of `{0, ..., n-1}` with exactly two positions
`i` (`i + 1 < n`) such that `σ(i+1) = σ(i) + 1` or `σ(i+1) + 1 = σ(i)` (the rising and
falling successions 12, 23, ..., 21, 32, ...). We checked by brute force that this gives
a(0..8) of %S.

Conjecture (R. J. Mathar, 2013): for `n ≥ 6` (the recurrence involves `a(n-6)`),
`(-514n+2465) a(n) + 2(257n^2-955n-1085) a(n-1) + (-555n^2+2483n-1670) a(n-2)
 + 16(-17n^2+73n-75) a(n-3) + (354n^2+528n-2299) a(n-4) + 2(-121n^2+1045n-1401) a(n-5)
 + 3(67n-115)(n-4) a(n-6) = 0`.
We checked it on the data for 6 ≤ n ≤ 22.
-/

namespace OMA.S_oeis_a086853

/-- The number of rising or falling successions of `σ`. -/
def successions (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i : Fin n =>
    ∃ h : i.val + 1 < n,
      ((σ ⟨i.val + 1, h⟩).val = (σ i).val + 1 ∨ (σ ⟨i.val + 1, h⟩).val + 1 = (σ i).val)).card

/-- `a(n)`: permutations of length `n` with exactly 2 successions. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ => successions n σ = 2).card

/-- Mathar's recurrence. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-514 * (n : ℤ) + 2465) * a n + 2 * (257 * (n : ℤ) ^ 2 - 955 * n - 1085) * a (n - 1)
      + (-555 * (n : ℤ) ^ 2 + 2483 * n - 1670) * a (n - 2)
      + 16 * (-17 * (n : ℤ) ^ 2 + 73 * n - 75) * a (n - 3)
      + (354 * (n : ℤ) ^ 2 + 528 * n - 2299) * a (n - 4)
      + 2 * (-121 * (n : ℤ) ^ 2 + 1045 * n - 1401) * a (n - 5)
      + 3 * (67 * (n : ℤ) - 115) * ((n : ℤ) - 4) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a086853
