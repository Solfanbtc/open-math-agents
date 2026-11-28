import Mathlib

/-!
# A136092: Bisection of A138540.

Source: https://oeis.org/A136092
Credit: @Solfanbtc

Claims (entry formulas, both marked conjectured, Michael D. Weiner, May 2016; see also
Gil–McNamara–Tirrell–Weiner, "From Dyck paths to standard Young tableaux", arXiv:1708.00513):
1. a(n) = Σ_{j=0..n+1} 180·(2n)!·(2j+2)!·(2n-3j+2) / (j!·(j+1)!·(j+2)!·(j+4)!·(n-j+1)!·(n-j+3)!)
   for every n ≥ 0 (computed in ℚ; individual terms may be negative or non-integral);
2. 36(n-1)(2n-1)(2n-3)·a(n-2) - 4(2n-1)(5n^2+22n+15)·a(n-1) + (n+3)(n+5)(n+6)·a(n) = 0 for every
   n ≥ 2 (so that a(n-2) is defined; offset 0).
Both are stated, as a conjunction.

Definition. a(n) = A138540(2n), where A138540(m) is the m-th moment of the trace of a Haar-random
matrix in USp(6). We use the equivalent description recorded in A138540 (Grabiner–Magyar): the
number of walks of length m on the cubic lattice ℤ^3, with unit steps ±e_i, starting and ending at
the origin and staying in the chamber x ≥ y ≥ z ≥ 0. A python check with this definition gives
all 18 listed terms 1, 1, 3, 15, 104, 909, ..., 293220749128031010 (and A138540(m) = 0 for odd m),
and both conjectured formulas for 0 ≤ n ≤ 60.
-/

namespace OMA.S_oeis_a136092

/-- The chamber x ≥ y ≥ z ≥ 0. -/
def InChamber (p : ℤ × ℤ × ℤ) : Prop := p.2.1 ≤ p.1 ∧ p.2.2 ≤ p.2.1 ∧ 0 ≤ p.2.2

instance : DecidablePred InChamber := fun p => by unfold InChamber; infer_instance

/-- The six unit steps ±e_i. -/
def steps : List (ℤ × ℤ × ℤ) := [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]

/-- Number of walks of length `m` from `p` to the origin with unit steps, every point after the
start lying in the chamber. -/
def walks : ℕ → ℤ × ℤ × ℤ → ℕ
  | 0, p => if p = (0, 0, 0) then 1 else 0
  | m + 1, p => ((steps.map fun s => p + s).filter fun q => decide (InChamber q)).map
      (walks m) |>.sum

/-- A138540(m): returning walks of length m in the chamber, from the origin. -/
def A138540 (m : ℕ) : ℕ := walks m (0, 0, 0)

/-- A136092(n) = A138540(2n). -/
def a (n : ℕ) : ℕ := A138540 (2 * n)

theorem main :
    (∀ n : ℕ, (a n : ℚ) = ∑ j ∈ Finset.range (n + 2),
        (180 * ((2 * n).factorial : ℚ) * ((2 * j + 2).factorial : ℚ) *
            ((2 * (n : ℤ) - 3 * j + 2 : ℤ) : ℚ)) /
          ((j.factorial : ℚ) * ((j + 1).factorial : ℚ) * ((j + 2).factorial : ℚ) *
            ((j + 4).factorial : ℚ) * ((n + 1 - j).factorial : ℚ) * ((n + 3 - j).factorial : ℚ))) ∧
    (∀ n : ℕ, 2 ≤ n →
      36 * ((n : ℤ) - 1) * (2 * n - 1) * (2 * n - 3) * a (n - 2)
        - 4 * (2 * (n : ℤ) - 1) * (5 * n ^ 2 + 22 * n + 15) * a (n - 1)
        + ((n : ℤ) + 3) * (n + 5) * (n + 6) * a n = 0) := by
  sorry

end OMA.S_oeis_a136092
