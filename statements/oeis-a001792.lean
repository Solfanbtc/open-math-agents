import Mathlib

/-!
# A001792: a(n) = (n+2)*2^(n-1).

Source: https://oeis.org/A001792
Credit: @Solfanbtc

Conjecture (Creighton Dement, Mar 14 2005): "Define a(-1) = 0 (as the sequence is returned by
FAMP). Then a(n-1) + A098156(n+1) = 2*a(n)."

Formalization notes:
* A001792 has offset 0: a(0), a(1), ... = 1, 3, 8, 20, 48, ... Since (n+2)*2^n is always even,
  a(n) = (n+2)*2^(n-1) is the natural number (n+2)*2^n / 2 (this gives a(0) = 1).
* A098156 (offset 0) is defined by its OEIS name: "Interleave n+1 and 2n+1 and take binomial
  transform". The interleaved sequence is c(2k) = k+1, c(2k+1) = 2k+1, i.e. 1, 1, 2, 3, 3, 5, ...,
  and A098156(n) = Sum_{k=0..n} binomial(n,k) * c(k) = 1, 2, 5, 13, 32, 76, ... (matches the
  OEIS data).
* The convention a(-1) = 0 is encoded by `aPrev`: `aPrev n` is a(n-1), with `aPrev 0 = 0`.
  The identity is stated for every n ≥ 0 (the indices used by the source).
* Checked in python for n < 300.
-/

namespace OMA.S_oeis_a001792

/-- A001792: a(n) = (n+2)*2^(n-1). -/
def a (n : ℕ) : ℕ := (n + 2) * 2 ^ n / 2

/-- a(n-1), with the source's convention a(-1) = 0. -/
def aPrev : ℕ → ℕ
  | 0 => 0
  | n + 1 => a n

/-- Interleave n+1 and 2n+1: c(2k) = k+1, c(2k+1) = 2k+1. -/
def interleave (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 + 1 else k

/-- A098156: the binomial transform of `interleave`. -/
def A098156 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * interleave k

/-- Dement's conjecture: a(n-1) + A098156(n+1) = 2*a(n) for all n ≥ 0, with a(-1) = 0. -/
theorem main : ∀ n : ℕ, aPrev n + A098156 (n + 1) = 2 * a n := by
  sorry

end OMA.S_oeis_a001792
