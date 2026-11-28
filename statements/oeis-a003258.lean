import Mathlib

/-!
# A003258: The number m such that c'(m) = A005206(A003231(n)), where c'(m) = A249115(m) is the m-th positive integer not in A003231.

Source: https://oeis.org/A003258
Credit: @Solfanbtc

Conjecture (Ralf Stephan, Feb 24 2004, OEIS A003258 and A078489): a(n) = A078489(n) + n - 1
for n >= 1.

Definitions, from the entries:
* A003231(n) = floor(n (sqrt 5 + 5) / 2), n >= 1.
* A249115(m) = floor(m (5 - sqrt 5) / 2), m >= 1: the m-th positive integer not in A003231
  (its Beatty complement). It is strictly increasing, so the m in the name is unique.
* A005206 is Hofstadter's G-sequence: G(0) = 0, G(n) = n - G(G(n - 1)) for n > 0. It is given
  here by its recurrence: `main` quantifies over every G satisfying it (exactly one does).
* A078489(n) = j such that binomial(n, j) < binomial(n - 1, j - 2). The PARI program of the entry
  takes the least j >= 0 with binomial(n, j) <= binomial(n - 1, j - 2) (it loops while >), with
  binomial(n - 1, j - 2) = 0 for j < 2, and that is what produces the data: with a strict < one
  gets a(2) = 3, not the listed a(2) = 2 (binomial(2,2) = binomial(1,0) = 1). Minimal fix: we use
  <= as in the program. For n >= 1, j = 0 and j = 1 never qualify (binomial(n, 0), binomial(n, 1)
  are positive), so the least j is taken over j >= 2.
* a(n) = A003258(n) is the m with A249115(m) = G(A003231(n)); since A249115 is injective, the
  conjecture says exactly that A249115(A078489(n) + n - 1) = G(A003231(n)).

Checked numerically: the 74 listed terms of A078489 and the 65 listed terms of A003258 are
reproduced by these definitions, and the conjecture holds for n < 2500.
-/

namespace OMA.S_oeis_a003258

/-- A003231(n) = floor(n (sqrt 5 + 5) / 2). -/
noncomputable def A003231 (n : ℕ) : ℕ := ⌊(n : ℝ) * (Real.sqrt 5 + 5) / 2⌋₊

/-- A249115(m) = floor(m (5 - sqrt 5) / 2), the m-th positive integer not in A003231. -/
noncomputable def A249115 (m : ℕ) : ℕ := ⌊(m : ℝ) * (5 - Real.sqrt 5) / 2⌋₊

/-- `j` is A078489(n): the least `j ≥ 2` with binomial(n, j) ≤ binomial(n - 1, j - 2). -/
def IsA078489 (n j : ℕ) : Prop :=
  IsLeast {i : ℕ | 2 ≤ i ∧ n.choose i ≤ (n - 1).choose (i - 2)} j

theorem main : ∀ G : ℕ → ℕ, G 0 = 0 → (∀ n : ℕ, 0 < n → G n = n - G (G (n - 1))) →
    ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, IsA078489 n j →
      A249115 (j + n - 1) = G (A003231 n) := by
  sorry

end OMA.S_oeis_a003258
