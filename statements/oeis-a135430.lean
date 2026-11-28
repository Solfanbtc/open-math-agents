import Mathlib

/-!
# A135430: Numbers k for which Ramanujan's function tau(k)=A000594(k) is an odd prime.

Source: https://oeis.org/A135430
Credit: @Solfanbtc

Ramanujan's tau function `τ(n)` (A000594) is defined by
`∑_{n ≥ 1} τ(n) qⁿ = q ∏_{k ≥ 1} (1 - q^k)^24`: `τ(1) = 1, τ(2) = -24, τ(3) = 252, ...`.

Conjecture (recorded in the entry, in Olivier Rozier's comment of Feb 03 2016): the equation
`|τ(n)| = 2` has no solution. Stated as: `|τ(n)| ≠ 2` for every `n ≥ 1`.
(The rest of the comment, that the terms of A135430 are of the form `p^(q-1)`, is derived there
from multiplicativity and the Lucas-sequence structure of `τ(p^k)`, and is not part of the
statement.) This is distinct from the upstream `RamanujanTau.lehmer_ramanujan_tau`
(`τ(n) ≠ 0`).

A python3 check: no `n < 2000` has `|τ(n)| = 2`; the first values agree with A000594.

Conventions: `τ(n) = [x^{n-1}] ∏_{k=1}^{n} (1 - x^k)^24` for `n ≥ 1` (the factors with `k ≥ n`
do not affect this coefficient), computed in `ℤ⟦X⟧`; `τ(0) = 0`.
-/

namespace OMA.S_oeis_a135430

open PowerSeries

/-- Ramanujan's tau function A000594. -/
noncomputable def τ (n : ℕ) : ℤ :=
  if n = 0 then 0 else coeff (n - 1) (∏ k ∈ Finset.Icc 1 n, ((1 : ℤ⟦X⟧) - X ^ k) ^ 24)

/-- Conjecture: `|τ(n)| = 2` has no solution. -/
theorem main : ∀ n : ℕ, 1 ≤ n → |τ n| ≠ 2 := by
  sorry

end OMA.S_oeis_a135430
