import Mathlib

/-!
# A030112: Antichains in fence × 7-chain; paths with n turns of light reflected from 8 glass plates.

Source: https://oeis.org/A030112
Credit: @Solfanbtc

Benoit Cloitre (Oct 16 2002, in the entry): "For a k-glass sequence, say a(n,k), a(n,k) is always
asymptotic to z(k)*w(k)^n where w(k)=(1/2)/cos(k*Pi/(2k+1)) and it is conjectured that z(k) is
the root 1<x<2 of a polynomial of degree Phi(2k+1)/2." (Phi = Euler's totient.)

Conventions.
* The k-glass sequence a(n,k) (number of paths with n turns of light reflected from k glass
  plates) is computed as in Cloitre's comment for k = 8: with `M(k)` the k × k 0/1 matrix with
  `M i j = 1` iff `i + j ≥ k - 1` (0-indexed) and `v = (1,...,1)`, a(n,k) is the last coordinate
  of `v * M(k)^n`, n ≥ 0. For k = 8 this gives 1, 8, 36, 204, 1086, 5916, ... (A030112, offset 0);
  for k = 2 it gives the Fibonacci numbers F(n+2) and for k = 3 A006356 (1, 3, 6, 14, ...).
  This indexing matters (a shift of n multiplies z(k) by w(k)); it is the one for which the
  entry's polynomial P(8, X) vanishes at z(8) ≈ 1.26420 (checked numerically).
* Range: the claim fails at k = 1 (one plate: a(n,1) = 1, w(1) = 1, so z(1) = 1, not in
  (1,2)); the minimal fix states it for k ≥ 2. Numerically (python3) z(k) ∈ (1.17, 1.28) for
  2 ≤ k ≤ 29.
* "the root 1<x<2 of a polynomial of degree Phi(2k+1)/2" is stated as: there is an integer
  polynomial P of degree φ(2k+1)/2 with P(z(k)) = 0, and z(k) is its only root in (1,2).
  (Numerically, for 2 ≤ k ≤ 13, among all the coefficients c_j in a(n,k) = Σ c_j λ_j^n, which
  contain the conjugates of z(k), only z(k) lies in (1,2).)
* The asymptotic statement (stated as a fact by Cloitre) is included: a(n,k)/w(k)^n → z(k).
-/

namespace OMA.S_oeis_a030112

/-- `glassVec k n = v * M(k)^n` with `M(k) i j = 1` iff `i + j ≥ k - 1`. -/
def glassVec (k : ℕ) : ℕ → Fin k → ℕ
  | 0 => fun _ => 1
  | n + 1 => fun j => ∑ i : Fin k, if k - 1 ≤ i.val + j.val then glassVec k n i else 0

/-- The k-glass sequence a(n,k): last coordinate of `v * M(k)^n`. -/
def glass (k n : ℕ) : ℕ :=
  if h : 0 < k then glassVec k n ⟨k - 1, by omega⟩ else 0

/-- w(k) = (1/2)/cos(kπ/(2k+1)). -/
noncomputable def w (k : ℕ) : ℝ := (1 / 2) / Real.cos (k * Real.pi / (2 * k + 1))

theorem main : ∀ k : ℕ, 2 ≤ k →
    ∃ z : ℝ, 1 < z ∧ z < 2 ∧
      Filter.Tendsto (fun n : ℕ => (glass k n : ℝ) / w k ^ n) Filter.atTop (nhds z) ∧
      ∃ P : Polynomial ℤ, P.natDegree = Nat.totient (2 * k + 1) / 2 ∧
        Polynomial.aeval z P = 0 ∧
        ∀ x : ℝ, 1 < x → x < 2 → Polynomial.aeval x P = 0 → x = z := by
  sorry

end OMA.S_oeis_a030112
