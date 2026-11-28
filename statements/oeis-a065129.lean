import Mathlib

/-!
# A065129: a(n) is the least m such that m/A003285(m) = n, or 0 if no such m exists.

Source: https://oeis.org/A065129
Credit: @Solfanbtc

`A003285(m)` is the period of the continued fraction of `√m` (`0` if `m` is a square).

Conjecture (in the entry): "`A003285(m)` = even or A004613, if `m` is divisible by `A003285(m)`",
where A004613 lists the numbers all of whose prime factors are `≡ 1 (mod 4)`. Stated literally:
for every nonsquare `m ≥ 1` whose period `A003285(m)` divides `m`, the period is even or all its
prime factors are `≡ 1 (mod 4)`. (The editorial gloss in the entry, that odd terms of A065129
lie in A004613, is not what is stated here.) Squares are excluded: their period is `0` by
convention and `0 ∤ m` for `m ≥ 1`, so they do not satisfy the hypothesis in the entry either.

Remark: this should follow from classical facts (an odd period of `√m` means the negative Pell
equation `x^2 - m y^2 = -1` is solvable, so every odd prime factor of `m` is `≡ 1 (mod 4)`);
the entry nevertheless records it as a conjecture, and it is stated as such here.

A python3 check (the standard `(m_k, d_k, a_k)` algorithm, reproducing the data of A003285): the
claim holds for all `2 ≤ m < 2·10^5` (802 such `m` have an odd period dividing `m`).

Conventions: the continued fraction is Mathlib's `GenContFract.of (√m)`; its partial
denominators `partDens` are `a_1, a_2, ...`, purely periodic for nonsquare `m`; the period is the
least `p > 0` with `partDens.get? (k + p) = partDens.get? k` for all `k`.
-/

namespace OMA.S_oeis_a065129

/-- The period of the continued fraction of `√m` (meaningful for nonsquare `m`). -/
noncomputable def period (m : ℕ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ ∀ k : ℕ,
    (GenContFract.of (Real.sqrt m)).partDens.get? (k + p) =
      (GenContFract.of (Real.sqrt m)).partDens.get? k}

/-- The conjecture: if the period of `√m` divides `m`, it is even or in A004613. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ¬ IsSquare m → period m ∣ m →
    Even (period m) ∨ ∀ p : ℕ, p.Prime → p ∣ period m → p % 4 = 1 := by
  sorry

end OMA.S_oeis_a065129
