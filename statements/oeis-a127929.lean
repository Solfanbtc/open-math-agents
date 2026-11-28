import Mathlib

/-!
# A127929: a(n) = A127928(n) mod 18.

Source: https://oeis.org/A127929
Credit: @Solfanbtc

Conjecture (entry comment): aside from 3, all terms of A127928 are 1 or 7 mod 18; "for large n,
the numbers of 1 and 7 mod 18 terms are approximately equal."

Definitions.
* Collatz map `C n = n/2` (n even), `3n + 1` (n odd). A positive integer `n` is impure if it
  occurs in the trajectory C(m), C(C(m)), ... of some smaller positive integer `m`, and pure
  otherwise (A061641; example of A127928: 5 is impure since it occurs in the trajectory of 3).
* A127928 lists the pure primes 3, 7, 19, 37, 43, ... (python3 reproduces its 54 data terms).
* "the numbers of 1 and 7 mod 18 terms are approximately equal" is read as: the number of pure
  primes p ≤ N with p ≡ 1 (mod 18), divided by the number with p ≡ 7 (mod 18), tends to 1.
  (Counting among the first n terms instead of up to N gives the same limit statement.)
  python3: up to 2*10^5 the counts are 2404 and 2951.
-/

namespace OMA.S_oeis_a127929

/-- The Collatz map. -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` is a pure hailstone number. -/
def IsPure (n : ℕ) : Prop := 0 < n ∧ ¬ ∃ m : ℕ, 0 < m ∧ m < n ∧ ∃ k : ℕ, 1 ≤ k ∧ C^[k] m = n

/-- Number of pure primes `p ≤ N` with `p ≡ r (mod 18)`. -/
noncomputable def count (r N : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p ≤ N ∧ p.Prime ∧ IsPure p ∧ p % 18 = r}

theorem main :
    Filter.Tendsto (fun N : ℕ => (count 1 N : ℝ) / count 7 N) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a127929
