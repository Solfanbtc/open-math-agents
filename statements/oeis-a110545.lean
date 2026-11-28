import Mathlib

/-!
# A110545: a(n) is smallest positive integer m such that n divides either the numerator or the denominator of the (reduced) fraction H(m) = Sum_{k=1..m} 1/k.

Source: https://oeis.org/A110545
Credit: @Solfanbtc

Conjecture (OEIS A110545, %C line): `a(n) ≤ n` for all positive `n`.

Formalization.
* `H(m) = harmonic m` (Mathlib, a rational in lowest terms); its reduced numerator and
  denominator are `(harmonic m).num` and `(harmonic m).den`.
* `a(n) ≤ n` says exactly that some `m` with `1 ≤ m ≤ n` has `n ∣ num H(m)` or `n ∣ den H(m)`
  (then the least such `m`, which is `a(n)`, exists and is `≤ n`; conversely `a(n) ≤ n` gives
  such an `m`). The statement is written in that form, which needs no separate definition of
  `a`.

Checked with python3 (exact fractions): the least such `m` reproduces all listed %S/%T/%U
terms (`n ≤ 81`), and `a(n) ≤ n` holds for `n ≤ 1200`.
-/

namespace OMA.S_oeis_a110545

/-- For every `n ≥ 1` some `H(m)` with `1 ≤ m ≤ n` has `n` dividing its reduced numerator or
its denominator, i.e. `a(n) ≤ n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ((n : ℤ) ∣ (harmonic m).num ∨ n ∣ (harmonic m).den) := by
  sorry

end OMA.S_oeis_a110545
