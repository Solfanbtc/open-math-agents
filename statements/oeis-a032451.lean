import Mathlib

/-!
# A032451: Aliquot sequences that reach 1 (Catalan's conjecture on iterating sigma(n) - n).

Source: https://oeis.org/A032451
Credit: @Solfanbtc

The entry (rows = aliquot sequences n, s(n), s(s(n)), ... that reach 1, where
s(n) = sigma(n) - n) says it is "Related to Catalan's conjecture about iterations of
f(n) = sigma(n) - n". The entry itself lists rows 6, 25, 28 as never reaching 1 (they reach the
perfect numbers 6 and 28).

Conventions.
* Catalan's conjecture (E. Catalan, 1888) asserted that every aliquot sequence ends at 1
  (hence 0) or at a perfect number; this original form is refuted by amicable pairs
  (220 -> 284 -> 220 never reaches 1 nor a perfect number). The conjecture in its standard,
  still open form (Catalan–Dickson conjecture, as corrected by Dickson in 1913) is that every
  aliquot sequence either terminates or becomes periodic (perfect, amicable or sociable
  cycle). For a sequence of naturals produced by iterating a fixed map, "eventually periodic"
  is equivalent to "bounded", which is what is stated: for every n the orbit
  n, s(n), s(s(n)), ... is bounded.
* s(n) = σ(n) - n is the sum of the proper divisors, `(Nat.properDivisors n).sum id`
  (with s(0) = 0, s(1) = 0); e.g. s(12) = 16, s(16) = 15, s(15) = 9, as in row 12 of the
  entry.
-/

namespace OMA.S_oeis_a032451

/-- The aliquot map s(n) = σ(n) - n. -/
def s (n : ℕ) : ℕ := ∑ d ∈ Nat.properDivisors n, d

theorem main : ∀ n : ℕ, ∃ B : ℕ, ∀ k : ℕ, s^[k] n ≤ B := by
  sorry

end OMA.S_oeis_a032451
