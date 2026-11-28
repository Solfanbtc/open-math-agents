import Mathlib

/-!
# A130058: Numbers m such that k = m*23^2 divides 3^(k-1) - 2^(k-1).

Source: https://oeis.org/A130058
Credit: @Solfanbtc

Conjecture (Alexander Adamchuk, May 04 2007, in A130058 and A073631): all nonsquarefree terms
of A073631 are the multiples of 23^2.

Definitions.
* A073631: nonprimes k (k ≥ 1; the data start with 1) such that k divides 3^(k-1) - 2^(k-1).
  python3 reproduces its data 1, 65, 133, 529, 793, 1105, ....
* "All nonsquarefree terms are the multiples of 23^2" is read as: every term of A073631 that is
  not squarefree is divisible by 529 = 23^2. (Not every multiple of 529 is a term; A130058
  lists those that are.) python3: true for all terms below 3*10^5.
(The related remark "It appears that 1 and 529 are the only perfect squares in A073631" is a
separate observation and is not part of this statement.)
-/

namespace OMA.S_oeis_a130058

/-- `k` is a term of A073631. -/
def InA073631 (k : ℕ) : Prop := 1 ≤ k ∧ ¬ k.Prime ∧ k ∣ 3 ^ (k - 1) - 2 ^ (k - 1)

theorem main : ∀ k : ℕ, InA073631 k → ¬ Squarefree k → 23 ^ 2 ∣ k := by
  sorry

end OMA.S_oeis_a130058
