import Mathlib

/-!
# A064390: Numbers of the form 2^k (2^n + 1) or 2^k (4^n - 2^n + 1)

Source: https://oeis.org/A064390
Credit: @Solfanbtc

A064390: `1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, …`, the numbers `2^k (2^n + 1)` or `2^k (4^n - 2^n + 1)`
with `k, n ≥ 0` (Gold and Kasami–Welch numbers times powers of 2; e.g. `1 = 4^0 - 2^0 + 1`,
`13 = 4^2 - 2^2 + 1`, `57 = 4^3 - 2^3 + 1`).

Conjecture (OEIS comment, after Janwa–McGuire–Wilson 1995 and Dillon 2002): call `m` exceptional
if the binary cyclic code of length `2^k - 1` with zeros `w` and `w^m` (`w` primitive in
`GF(2^k)`) is double-error-correcting for infinitely many `k`. It is conjectured that this
sequence, with the powers of 2 omitted, gives all exceptional `m`'s.

Formalization. For `k`, `w ∈ GF(2^k)` (Mathlib's `GaloisField 2 k`) is primitive when its order is
`2^k - 1`. A word is `c : Fin (2^k - 1) → ZMod 2`; it is in the code when `c(w) = ∑ c_i w^i = 0`
and `c(w^m) = 0`. The code is double-error-correcting iff its minimum distance is `≥ 5`, i.e.
every nonzero codeword has at least 5 nonzero coordinates. The property does not depend on the
primitive element (another one is `w^j` with `gcd(j, 2^k - 1) = 1`, and `i ↦ i j` permutes the
coordinates), so it is required for all primitive `w`. "Gives all exceptional `m`'s" is read as
"is exactly the set of exceptional `m ≥ 1`" (the sequence members other than powers of 2 are the
exceptional numbers). (A brute force of this model for `k = 4, 6` gives exactly the
double-error-correcting `m < 2^k - 1`: `3, 6, 9, 12` and `3, 6, 12, 24, 33, 48`.) A proof of this
classification was published by F. Hernando and G. McGuire (J. Algebra 343, 2011); this is not
recorded in the entry.
-/

namespace OMA.S_oeis_a064390

/-- The binary cyclic code of length `2^k - 1` with zeros `w` and `w^m` is double-error-correcting
(minimum distance `≥ 5`) for every primitive `w ∈ GF(2^k)`. -/
def IsDEC (m k : ℕ) : Prop :=
  ∀ w : GaloisField 2 k, orderOf w = 2 ^ k - 1 →
    ∀ c : Fin (2 ^ k - 1) → ZMod 2, c ≠ 0 →
      (∑ i, algebraMap (ZMod 2) (GaloisField 2 k) (c i) * w ^ (i : ℕ)) = 0 →
      (∑ i, algebraMap (ZMod 2) (GaloisField 2 k) (c i) * (w ^ m) ^ (i : ℕ)) = 0 →
      5 ≤ (Finset.univ.filter fun i => c i ≠ 0).card

/-- `m` is exceptional: double-error-correcting for infinitely many `k`. -/
def Exceptional (m : ℕ) : Prop := {k : ℕ | IsDEC m k}.Infinite

/-- `m` is a term of A064390. -/
def InA (m : ℕ) : Prop :=
  ∃ k n : ℕ, m = 2 ^ k * (2 ^ n + 1) ∨ m = 2 ^ k * (4 ^ n - 2 ^ n + 1)

/-- The exceptional `m ≥ 1` are exactly the terms of A064390 that are not powers of 2. -/
theorem main : ∀ m : ℕ, 1 ≤ m → (Exceptional m ↔ InA m ∧ ¬ ∃ j : ℕ, m = 2 ^ j) := by
  sorry

end OMA.S_oeis_a064390
