import Mathlib

/-!
# A005846: Primes of the form k^2 + k + 41.

Source: https://oeis.org/A005846
Credit: @Solfanbtc

Context (the entry): `n² + n + 41` is prime for `n = 0, ..., 39`. A comment by Luis Rodriguez
(Jun 22 2008) disputes the claim that for every `A` some polynomial `n² + n + B` gives primes for
`n = 0, ..., A`.

Claim (T. D. Noe, Aug 31 2009, in the entry): contrary to that comment, Mollin's Theorem 2.1
shows that any `A` is possible if the prime k-tuples conjecture is assumed. Stated as:
prime k-tuples conjecture → for every `A` there is `B` with `n² + n + B` prime for all
`0 ≤ n ≤ A`. (R. A. Mollin, "Prime-producing quadratics", Amer. Math. Monthly 104 (1997)
529-544.)

Conventions:
* A finite set `H ⊆ ℕ` is admissible if for every prime `p` some residue `r < p` has `p ∤ r + h`
  for all `h ∈ H` (`H` does not cover all residues mod `p`).
* Prime k-tuples conjecture (Dickson; qualitative Hardy–Littlewood): for every admissible `H`
  there are infinitely many `m` with `m + h` prime for all `h ∈ H`.
* (Why it applies: `n² + n + B = B + n(n+1)`, and `{n(n+1) : n ≤ A}` is admissible since
  `n(n+1)` is always even and takes only `(p+1)/2` residues mod an odd prime `p`. This is a
  remark, not part of the statement.)
-/

namespace OMA.S_oeis_a005846

/-- `H` is admissible: it misses some residue class modulo every prime. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r < p, ∀ h ∈ H, ¬ p ∣ r + h

/-- The prime k-tuples conjecture. -/
def PrimeKTuplesConjecture : Prop :=
  ∀ H : Finset ℕ, Admissible H → ∀ N : ℕ, ∃ m > N, ∀ h ∈ H, (m + h).Prime

/-- Assuming the prime k-tuples conjecture, for every `A` some `n² + n + B` is prime for all
`n = 0, ..., A`. -/
theorem main : PrimeKTuplesConjecture → ∀ A : ℕ, ∃ B : ℕ, ∀ n ≤ A, (n ^ 2 + n + B).Prime := by
  sorry

end OMA.S_oeis_a005846
