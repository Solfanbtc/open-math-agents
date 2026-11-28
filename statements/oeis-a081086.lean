import Mathlib

/-!
# A081086: Smallest partial quotients of an infinite simple continued fraction such that the fractional remainders sum to unity.

Source: https://oeis.org/A081086
Credit: @Solfanbtc

For partial quotients `a(1), a(2), …` the fractional remainders are `x_k = [0; a(k), a(k+1), …]`,
and the entry asks for `∑_k x_k = 1` with the partial quotients chosen as small as possible,
one after another (the example: `1 = [0;2,2,9,91,…] + [0;2,9,91,…] + [0;9,91,…] + ⋯`).
The construction is greedy, and is formalized as follows. Once `a(1), …, a(n-1)` are fixed,
`a(n)` is the least positive integer `a` such that the remainders of the finite continued
fraction `[0; a(1), …, a(n-1), a]` still sum to less than 1:
`∑_{k=1}^{n} [0; a(k), …, a(n-1), a] < 1`. (Such `a` exists: large `a` gives a sum close to the
previous one, which is `< 1`.)
Checked with python3 (exact rationals): this rule gives exactly the listed terms 2, 2, 9, 91,
14201, 252238179, 82413709268226496, 12393783734739289765092773334814410. The first four were
found by exhaustive search; for the others the least `a` was located by bisection, and `a - 1`
was checked to fail.

Conjecture (H. Havermann and P. D. Hanna): `log a(n+1) / log a(n) → 2`. `main` states this.
-/

namespace OMA.S_oeis_a081086

open Filter Topology Real

/-- The finite continued fraction `[0; l₁, l₂, …, l_m]`. -/
def cf : List ℕ → ℚ
  | [] => 0
  | x :: l => 1 / ((x : ℚ) + cf l)

/-- Sum of the fractional remainders `[0; l_k, …, l_m]`, `k = 1, …, m`. -/
def remSum (l : List ℕ) : ℚ := ∑ k ∈ Finset.range l.length, cf (l.drop k)

/-- `firstTerms n = [a(1), …, a(n)]`. -/
noncomputable def firstTerms : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let l := firstTerms n
    l ++ [sInf {a : ℕ | 1 ≤ a ∧ remSum (l ++ [a]) < 1}]

/-- `a n`: the `n`-th term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (firstTerms n).getD (n - 1) 0

theorem main :
    Tendsto (fun n : ℕ => log (a (n + 1) : ℝ) / log (a n : ℝ)) atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a081086
