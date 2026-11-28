import Mathlib

/-!
# A000232: Construct a triangle as in A036262. Sequence is one less than the position of the first number larger than 2 in the n-th row (n-th difference).

Source: https://oeis.org/A000232
Credit: @Solfanbtc

Claim (Bartlomiej Pawlik, Nov 28 2025, in the %C lines): if `a(n) > 2` for every `n`, then the
Gilbreath conjecture is true.

Formalization:
* The triangle A036262 (Gilbreath's array): row `0` is the primes `2, 3, 5, 7, …` and row `n+1`
  is the sequence of absolute differences of consecutive terms of row `n`. We write `d n k` for
  the `k`-th entry (from `k = 0`) of row `n`, with `d 0 k = Nat.nth Nat.Prime k` (as in
  `Gilbreath.d` of formal-conjectures).
* `a(n)` (offset 1) is one less than the 1-based position of the first entry `> 2` of row `n`,
  i.e. the 0-based index `k` of that entry. (This reproduces `a(1) = 3`, `a(2) = 8`,
  `a(3) = 14`, …: row 1 is `1, 2, 2, 4, …`.) "`a(n) > 2`" is therefore: row `n` has an entry
  `> 2`, and the first one has 0-based index `k > 2`, i.e. `k ≥ 3`.
* The Gilbreath conjecture: the first entry of every row `n ≥ 1` is `1`.
The claim is the implication, stated as such.
-/

namespace OMA.S_oeis_a000232

/-- Gilbreath's array A036262: `d 0 k` is the `k`-th prime (from `k = 0`), and row `n + 1` is the
absolute differences of consecutive entries of row `n`. -/
noncomputable def d : ℕ → ℕ → ℕ
  | 0 => fun k => Nat.nth Nat.Prime k
  | n + 1 => fun k => Int.natAbs ((d n (k + 1) : ℤ) - d n k)

/-- `a(n) > 2`: row `n` has an entry larger than `2`, and the first such entry sits at 0-based
index `k ≥ 3` (that index is `a(n)`). -/
def AGtTwo (n : ℕ) : Prop :=
  ∃ k, 3 ≤ k ∧ 2 < d n k ∧ ∀ j < k, d n j ≤ 2

/-- Pawlik: if `a(n) > 2` for every `n ≥ 1`, then the Gilbreath conjecture holds. -/
theorem main : (∀ n : ℕ, 1 ≤ n → AGtTwo n) → ∀ n : ℕ, 1 ≤ n → d n 0 = 1 := by
  sorry

end OMA.S_oeis_a000232
