import Mathlib

/-!
# A117846: eventual common difference of b(k+1) = b(k) + (b(k) mod k), b(1) = 2n - 1.

Source: https://oeis.org/A117846 (Alex Abercrombie, 2007; OEIS Foundation, CC BY-SA 4.0).
Related: A073117 (the case b(1) = 1), A066910.
Credit: @Solfanbtc

Definition (OEIS): given n ≥ 1, let b(1) = 2n - 1 and b(k+1) = b(k) + (b(k) mod k), where
b(k) mod k is the least nonnegative residue. a(n) is the common value of b(k+1) - b(k) for all
large k if such exists; otherwise a(n) = 0.

Conjecture (OEIS comment): "a(n) is never zero; that is all the sequences b(k) are arithmetic
progressions from some point on."

Formalization notes.
* `b n k` is the OEIS b(k) for k ≥ 1 (the value at k = 0 is an unused placeholder, equal to
  b(1)); the offset of A117846 is 1, so n ranges over n ≥ 1.
* "a(n) is never zero" means: the common value exists and is nonzero. We state exactly that:
  there are d > 0 and K such that b(k+1) - b(k) = d for all k ≥ K.
* The final question of the comment ("Do the values a(n) include all positive numbers?") is a
  question, not a conjecture, and is not stated.
* A python computation (200000 steps per n) reproduces all 68 listed terms.
-/

namespace OMA.S_oeis_a117846

/-- `b n k` is b(k) for k ≥ 1, with b(1) = 2n - 1 and b(k+1) = b(k) + (b(k) mod k). -/
def b (n : ℕ) : ℕ → ℕ
  | 0 => 2 * n - 1
  | 1 => 2 * n - 1
  | k + 2 => b n (k + 1) + b n (k + 1) % (k + 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ d : ℕ, 0 < d ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → b n (k + 1) = b n k + d := by
  sorry

end OMA.S_oeis_a117846
