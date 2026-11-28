import Mathlib

/-!
# A078798: Sum of Manhattan distances over self-avoiding n-step walks on the square lattice

Source: https://oeis.org/A078798
Credit: @Solfanbtc

Self-avoiding `n`-step walks on `ℤ^2` from the origin with the first step specified (to the right),
as in A046661 (`c(n)`: `1, 3, 9, 25, 71, …`, the denominator of the mean displacement);
`a(n)` (offset 1) is the sum over these walks of the Manhattan distance `|x| + |y|` of the
endpoint: `1, 6, 23, 80, 263, …`, and `s(n) = a(n)/c(n)` is the mean Manhattan displacement. A walk
is a step sequence `d : Fin n → Fin 4` (right, left, up, down) with first step right whose
positions `p_0 = 0, p_1, …, p_n` are pairwise distinct. (A brute force with this model reproduces
the first 10 terms of both A078798 and A046661.)

Conjecture (OEIS comment, illustrated by Hugo Pfoertner's plots): `lim_{n→∞} a(n)/(c(n) n^(3/4))`
`= constant`. Stated as: there is a constant `C > 0` with `a(n)/(c(n) n^(3/4)) → C` (the constant
is positive in the intended asymptotic `s(n) ~ C n^(3/4)`; the limit `0` would not describe the
behaviour `n^(3/4)`).
-/

namespace OMA.S_oeis_a078798

/-- The four unit steps. -/
def vec : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Position after the first `k` steps. -/
def pos {n : ℕ} (d : Fin n → Fin 4) (k : ℕ) : ℤ × ℤ :=
  ∑ i : Fin n, if (i : ℕ) < k then vec (d i) else 0

/-- `d` is a self-avoiding walk with first step to the right. -/
def IsSAW {n : ℕ} (d : Fin n → Fin 4) : Prop :=
  (∀ i : Fin n, (i : ℕ) = 0 → d i = 0) ∧
    ∀ j ∈ Finset.range (n + 1), ∀ k ∈ Finset.range (n + 1), pos d j = pos d k → j = k

instance {n : ℕ} : DecidablePred (@IsSAW n) := fun d => by unfold IsSAW; infer_instance

/-- A046661: the number of such walks. -/
def c (n : ℕ) : ℕ := (Finset.univ.filter fun d : Fin n → Fin 4 => IsSAW d).card

/-- A078798: the sum of the Manhattan distances of their endpoints. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.univ.filter (fun d : Fin n → Fin 4 => IsSAW d),
    ((pos d n).1.natAbs + (pos d n).2.natAbs)

/-- Conjectured asymptotics of the mean Manhattan displacement: `a(n)/(c(n) n^(3/4)) → C > 0`. -/
theorem main : ∃ C : ℝ, 0 < C ∧ Filter.Tendsto
    (fun n : ℕ => (a n : ℝ) / ((c n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 4))) Filter.atTop (nhds C) := by
  sorry

end OMA.S_oeis_a078798
