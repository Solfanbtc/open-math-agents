import Mathlib

/-!
# A105875: Primes for which -3 is a primitive root.

Source: https://oeis.org/A105875
Credit: @Solfanbtc

A105875 lists the primes `p` for which `-3` is a primitive root modulo `p`, i.e. the
multiplicative order of `-3` in `ZMod p` is `p - 1`.

Claim (in the entry): on Artin's conjecture, the number of terms `≤ N` is asymptotically
equivalent to `(6/5) · C · π(N)`, where `C = A005596 = ∏_p (1 - 1/(p(p-1)))` is Artin's
constant. (`-3` is not a perfect power and its squarefree part `-3 ≡ 1 (mod 4)`, so Artin's
conjecture in Heilbronn's corrected form predicts the density `C · (1 + 1/(3² - 3 - 1)) = (6/5) C`;
this case, `a₀ ≡ 1 (mod 4)` for a non-power `a`, is not among the upstream statements
`ArtinPrimitiveRootsConjecture.*`.) Stated as the predicted asymptotic itself:
`#{p ≤ N : p ∈ A105875} / π(N) → (6/5) C`.

A python3 check: among the primes up to `2·10⁶` the proportion is `0.448752`, against
`(6/5) C = 0.448747`.

Conventions: the set of primes and Artin's constant are defined as in the upstream file
`FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean` (`S a`, `ArtinConstant`);
`π(N) = Nat.primeCounting N`.
-/

namespace OMA.S_oeis_a105875

open Filter Topology

/-- Primes `p` for which `-3` is a primitive root modulo `p`. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ orderOf ((-3 : ℤ) : ZMod p) = p - 1

/-- Artin's constant `∏_p (1 - 1/(p(p-1)))` (A005596). -/
noncomputable def ArtinConstant : ℝ := ∏' p : Nat.Primes, (1 - 1 / (p * (p - 1)) : ℝ)

/-- On Artin's conjecture: `#{p ≤ N : -3 primitive root mod p} ~ (6/5) C π(N)`. -/
theorem main :
    Tendsto (fun N : ℕ => (({p : ℕ | p ≤ N ∧ IsTerm p}.ncard : ℕ) : ℝ) / Nat.primeCounting N)
      atTop (𝓝 (6 / 5 * ArtinConstant)) := by
  sorry

end OMA.S_oeis_a105875
