import Mathlib

/-!
# A071060: Largest n-digit prime with only prime digits.

Source: https://oeis.org/A071060
Credit: @Solfanbtc

Conjecture (OEIS entry, %F, Bill McEachen 2023): `a(n) ~ floor((7/9) * 10^n)`.

Conventions:
* Offset 1. A number `p` is `n`-digit when `(Nat.digits 10 p).length = n` (no leading zeros);
  its digits are prime when each decimal digit is one of `2, 3, 5, 7`.
* `a(n)` is the supremum (`sSup`) of the set of such primes. The set is finite (all elements are
  below `10^n`), so when it is nonempty `a(n)` is its largest element. When it is empty `sSup`
  gives `0`; the asymptotic equivalence then forces the set to be nonempty for all large `n`, as the
  source implicitly assumes (a(n) is listed for every `n`).
* `~` is `Asymptotics.IsEquivalent` as `n → ∞`; `floor((7/9) * 10^n)` is `7 * 10^n / 9`
  (natural division), i.e. the repunit-like number `77…7` with `n` sevens.
* Checked in Python: the brute-force definition reproduces all 23 listed terms (%S, %T, %U).
-/

namespace OMA.S_oeis_a071060

open Filter Asymptotics

/-- `p` is an `n`-digit prime all of whose decimal digits are prime. -/
def IsPrimeDigitPrime (n p : ℕ) : Prop :=
  p.Prime ∧ (Nat.digits 10 p).length = n ∧ ∀ d ∈ Nat.digits 10 p, d ∈ ({2, 3, 5, 7} : Finset ℕ)

/-- `a(n)`: the largest `n`-digit prime with only prime digits. -/
noncomputable def a (n : ℕ) : ℕ := sSup {p | IsPrimeDigitPrime n p}

/-- The conjecture of A071060: `a(n) ~ floor((7/9) * 10^n)`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => ((7 * 10 ^ n / 9 : ℕ) : ℝ)) := by
  sorry

end OMA.S_oeis_a071060
