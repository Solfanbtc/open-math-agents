import Mathlib

/-!
# A073155: Leftmost column sequence of triangle A073153.

Source: https://oeis.org/A073155
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Nov 26 2012, in the %F lines):
  `(n+1) a(n) + (-3n+4) a(n-1) + 2(-6n+7) a(n-2) + 2(-6n+11) a(n-3) + 2(-2n+5) a(n-4) = 0`.

Formalization:
* `a(n)` is given by the closed form stated in the entry,
  `a(n) = Sum_{k=0..n} C(2k, n-k) * C(k)` (Paul Barry, Jul 09 2006), where `C(k)` is the Catalan
  number (Mathlib's `catalan`); it reproduces the listed terms `1, 1, 4, 14, 56, 237, 1046, …`
  (offset 0), which also satisfy the defining convolution
  `a(n+1) = Sum_{k=0..n} (a(k) + a(k-1)) (a(n-k) + a(n-k-1))`, `a(-1) = 0`.
* The term `a(n-4)` must exist, so the recurrence is stated for `n ≥ 4` (we write `n + 4` for
  `n`), in `ℤ`. It was checked numerically for all `4 ≤ n < 100`.
-/

namespace OMA.S_oeis_a073155

/-- A073155: `a(n) = Sum_{k=0..n} C(2k, n-k) * Catalan(k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * k) (n - k) * catalan k

/-- Mathar's conjectured recurrence, for `n ≥ 4`. -/
theorem main : ∀ m : ℕ, let n : ℤ := (m : ℤ) + 4
    (n + 1) * (a (m + 4) : ℤ) + (-3 * n + 4) * (a (m + 3) : ℤ)
      + 2 * (-6 * n + 7) * (a (m + 2) : ℤ) + 2 * (-6 * n + 11) * (a (m + 1) : ℤ)
      + 2 * (-2 * n + 5) * (a m : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a073155
