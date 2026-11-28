import Mathlib

/-!
# A073008: Decimal expansion of the Traveling Salesman constant.

Source: https://oeis.org/A073008
Credit: @Solfanbtc

Conjecture (OEIS A073008, %F line): the Traveling Salesman constant equals
(4/153) (1 + 2 sqrt 2) sqrt 51 = 0.71478...

The constant (entry comment by Elijah Beregovsky, Jan 10 2020): Beardwood, Halton and Hammersley
(1959) showed that the shortest tour through N independent uniformly distributed random points in
a bounded plane region of area A is asymptotic to K sqrt(N A); K is the Traveling Salesman
constant. We use the unit square [0,1]^2 (A = 1) and the convergence of the mean, which BHH also
proved: K = lim_{N→∞} E[L_N] / sqrt N, where L_N is the length of a shortest closed tour through
N uniform points. Here:
* points are in ℝ × ℝ with the Euclidean distance written out (`euclid`), not the sup metric
  that Mathlib puts on products;
* a closed tour visits the points in the order σ(0), σ(1), ..., σ(N-1), σ(0) for a permutation σ
  (`finRotate` sends i to i + 1 mod N); L_N is the minimum over σ;
* the N points are uniform in the unit square, so E[L_N] is the Lebesgue integral of L_N over
  ([0,1]^2)^N, a set of volume 1.
`main` states that E[L_N] / sqrt N tends to (4/153)(1 + 2 sqrt 2) sqrt 51.
-/

namespace OMA.S_oeis_a073008

open Filter MeasureTheory

/-- Euclidean distance in the plane. -/
noncomputable def euclid (p q : ℝ × ℝ) : ℝ := Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- Length of the closed tour visiting `x (σ 0), x (σ 1), …, x (σ (N-1))` and back. -/
noncomputable def tourLength {N : ℕ} (x : Fin N → ℝ × ℝ) (σ : Equiv.Perm (Fin N)) : ℝ :=
  ∑ i, euclid (x (σ i)) (x (σ (finRotate N i)))

/-- Length of a shortest closed tour through the points `x`. -/
noncomputable def tsp {N : ℕ} (x : Fin N → ℝ × ℝ) : ℝ := ⨅ σ : Equiv.Perm (Fin N), tourLength x σ

/-- The configurations of `N` points in the unit square. -/
def unitSquareConfigs (N : ℕ) : Set (Fin N → ℝ × ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1}

theorem main :
    Tendsto (fun N : ℕ => (∫ x in unitSquareConfigs N, tsp x) / Real.sqrt N) atTop
      (nhds ((4 / 153) * (1 + 2 * Real.sqrt 2) * Real.sqrt 51)) := by
  sorry

end OMA.S_oeis_a073008
