import Mathlib

/-!
# A001387: Binary "look and say" sequence.

Source: https://oeis.org/A001387
Credit: @Solfanbtc

Conjecture (Joseph L. Pe, Jan 31 2003, OEIS A001387): the ratio r(n) of the number of 1s to the
number of 0s in a(n) converges to 5/3 (or some nearby limit).

The entry then records (Nathaniel Johnston, Nov 07 2010, corrected by Kevin J. Gomez,
Dec 12 2017) that r(n) actually converges to
  ((101 - 10 sqrt 93) α^2 + (139 - 13 sqrt 93) α - 76) / 108,  α = (116 + 12 sqrt 93)^(1/3),
which is 1.6657272222676... Pe's limit is imprecise (5/3 or some nearby value), so `main` states
this precise form recorded in the entry: r(n) tends to that constant.

Conventions: a term is the list of its binary digits, most significant first; a(1) = 1 is
`term 0`. One step reads the runs of equal digits from left to right and replaces a run of c
copies of the digit d by the binary expansion of c (most significant first) followed by d,
e.g. 111011 ↦ 11 1 1 0 10 1 = 11110101. The first seven values of `term` are the %S data
1, 11, 101, 111011, 11110101, 100110111011, 111001011011110101.
Every term has at least one 0 from a(2) on (a(1) = 1 gives r = 0 by Lean's x / 0 = 0, which
does not affect the limit). Simulated up to a(44): r ≈ 1.6657274.
-/

namespace OMA.S_oeis_a001387

/-- One binary look-and-say step on a list of binary digits (most significant first). -/
def step (l : List ℕ) : List ℕ :=
  (l.splitBy (· == ·)).flatMap fun g => (Nat.digits 2 g.length).reverse ++ [g.headD 0]

/-- `term n` is a(n + 1), as a list of binary digits. -/
def term (n : ℕ) : List ℕ := step^[n] [1]

/-- r(n + 1): number of 1s divided by number of 0s in a(n + 1). -/
noncomputable def ratio (n : ℕ) : ℝ := ((term n).count 1 : ℝ) / ((term n).count 0 : ℝ)

/-- The limit constant recorded in the entry. -/
noncomputable def limitConst : ℝ :=
  let α : ℝ := (116 + 12 * Real.sqrt 93) ^ ((1 : ℝ) / 3)
  ((101 - 10 * Real.sqrt 93) * α ^ 2 + (139 - 13 * Real.sqrt 93) * α - 76) / 108

theorem main : Filter.Tendsto ratio Filter.atTop (nhds limitConst) := by
  sorry

end OMA.S_oeis_a001387
