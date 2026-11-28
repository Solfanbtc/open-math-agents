import Mathlib

/-!
# A091457: Greatest numerator of the remainder in a reciprocal expansion of 1.

Source: https://oeis.org/A091457
Credit: @Solfanbtc

An expansion of length `n` is `1 = 1/x_1 + ... + 1/x_{n-1} + p/q` with positive integers
`x_1 ≤ ... ≤ x_{n-1}` (i.e. `1/x_1 ≥ ... ≥ 1/x_{n-1}`), a remainder `p/q` in lowest terms with
`1/x_{n-1} ≥ p/q`, and `p/q > 0` (remainder 0 has numerator 0 and never matters for the
maximum). `a(n)` is the maximal `p`. Example: a(7) = 9770455, attained by
1 = 1/2 + 1/3 + 1/7 + 1/43 + 1/5413 + 1/5419 + 9770455/52975482882.

Conjecture (Max Alekseyev, 2004): "in the extremal expansion x_i = A000058(i) for i=1..n-3".
A000058 (Sylvester's sequence 2, 3, 7, 43, 1807, ...) has offset 0, and in the entry's own
example x_1, ..., x_4 = 2, 3, 7, 43 = A000058(0), ..., A000058(3); read with A000058(i) the
claim would already fail at n = 4 (x_1 = 2 ≠ A000058(1) = 3). Minimal fix: x_i = A000058(i-1)
for `i = 1, ..., n-3`. We checked by exhaustive search for n ≤ 6 that the maximizer is unique:
(2, 3, 11), (2, 3, 11, 25), (2, 3, 7, 121, 127), with maxima 5, 59, 4951 as in the data.
`main` states it for every expansion attaining the maximum, for every `n ≥ 4` (for `n ≤ 3`
there is nothing to state). Indices are 0-based below: `x ⟨j, _⟩` is `x_{j+1}`.
-/

namespace OMA.S_oeis_a091457

/-- Sylvester's sequence A000058: `s 0 = 2`, `s (k+1) = s k ^ 2 - s k + 1`. -/
def sylvester : ℕ → ℕ
  | 0 => 2
  | k + 1 => sylvester k ^ 2 - sylvester k + 1

/-- The remainder `1 - Σ 1/x_i`. -/
def rem {m : ℕ} (x : Fin m → ℕ) : ℚ := 1 - ∑ i, (1 : ℚ) / x i

/-- `x` gives an expansion: positive nondecreasing denominators, `0 < rem x ≤ 1/x_i`. -/
def IsExpansion {m : ℕ} (x : Fin m → ℕ) : Prop :=
  (∀ i, 0 < x i) ∧ Monotone x ∧ 0 < rem x ∧ ∀ i, rem x ≤ (1 : ℚ) / x i

/-- Alekseyev's conjecture (with the index shift explained above). -/
theorem main : ∀ n : ℕ, 4 ≤ n → ∀ x : Fin (n - 1) → ℕ, IsExpansion x →
    (∀ y : Fin (n - 1) → ℕ, IsExpansion y → (rem y).num ≤ (rem x).num) →
    ∀ i : Fin (n - 1), (i : ℕ) < n - 3 → x i = sylvester i := by
  sorry

end OMA.S_oeis_a091457
