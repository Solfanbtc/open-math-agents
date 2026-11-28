import Mathlib

/-!
# A006356: a(n) = 2*a(n-1) + a(n-2) - a(n-3) for n >= 3, starting with a(0) = 1, a(1) = 3, and a(2) = 6.

Source: https://oeis.org/A006356
Credit: @Solfanbtc

The source's claim: for a k-glass sequence a(n,k), a(n,k) is always asymptotic to
z(k)*w(k)^n where w(k) = (1/2)/cos(k*Pi/(2*k+1)), and it is conjectured that z(k) is the
root 1 < x < 2 of a polynomial of degree Phi(2k+1)/2 (Phi = Euler's totient).

The k-glass sequence: a(n,k) is the number of paths of a ray of light that enters a stack of
k glass plates and is reflected exactly n times before leaving (k = 2 gives the Fibonacci
numbers F(n+2), k = 3 gives A006356, k = 4 gives A006357). Number the k+1 faces 0 (top) to
k (bottom); the ray enters through face 0 going down. Moving down it can reflect at a face
strictly below its last reflection (or below face 0 at the start), moving up at a face
strictly above it. So a(n,k) counts the sequences 0 = f 0 < f 1 > f 2 < f 3 > ... (n steps)
with every value in {0, ..., k}. This is `glass k n`; it gives 1, 3, 6, 14, 31, 70, 157 for
k = 3 and 1, 2, 3, 5, 8, 13 for k = 2, as checked by computation.

Reading of the claim:
* z(k) is the limit of a(n,k)/w(k)^n (which is what the asymptotic says, z(k) > 0 here).
* "a polynomial of degree Phi(2k+1)/2" is read as the minimal polynomial of z(k) over ℚ:
  z(k) always lies in ℚ(cos(π/(2k+1))), of degree Phi(2k+1)/2, so some (reducible) rational
  polynomial of that degree vanishes at z(k) for trivial reasons; the content of the
  conjecture is that z(k) has exactly that algebraic degree.
* "the root 1 < x < 2" is read as: z(k) is a root lying in (1,2), and the only root of that
  polynomial in (1,2).
* Minimal fix: k ≥ 2. For k = 1 there is one path for every n, w(1) = 1 and z(1) = 1, which is
  not in the open interval (1,2); the source's k-glass sequences start at k = 2 (Fibonacci).
Numerically (eigen-decomposition of the transfer matrix) the claim holds for 2 ≤ k ≤ 19.
-/

namespace OMA.S_oeis_a006356

open Filter Topology Polynomial

/-- a(n,k): the number of sequences `f 0 = 0 < f 1 > f 2 < f 3 > ...` of length `n + 1`
with values in `{0, ..., k}` (light paths through `k` glass plates with `n` reflections). -/
def glass (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin (n + 1) → Fin (k + 1) =>
    f 0 = 0 ∧ ∀ i : Fin n,
      if Even (i : ℕ) then f i.castSucc < f i.succ else f i.succ < f i.castSucc).card

/-- w(k) = (1/2)/cos(k*Pi/(2*k+1)). -/
noncomputable def w (k : ℕ) : ℝ :=
  (1 / 2) / Real.cos (k * Real.pi / (2 * k + 1))

theorem main : ∀ k : ℕ, 2 ≤ k → ∃ z : ℝ,
    Tendsto (fun n : ℕ => (glass k n : ℝ) / w k ^ n) atTop (𝓝 z) ∧
    1 < z ∧ z < 2 ∧ IsIntegral ℚ z ∧
    (minpoly ℚ z).natDegree = Nat.totient (2 * k + 1) / 2 ∧
    ∀ x ∈ Set.Ioo (1 : ℝ) 2, aeval x (minpoly ℚ z) = 0 → x = z := by
  sorry

end OMA.S_oeis_a006356
