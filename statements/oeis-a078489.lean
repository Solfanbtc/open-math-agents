import Mathlib

/-!
# A078489: a(n)=j such that binomial(n,j)<binomial(n-1,j-2).

Source: https://oeis.org/A078489
Credit: @Solfanbtc

`a(n)` (`n ≥ 1`) is the first `j = 0, 1, 2, …` at which `binomial(n, j) > binomial(n-1, j-2)`
fails, with `binomial(n-1, j-2) = 0` for `j < 2` (the PARI program of the entry:
`while (binomial(n,j)>binomial(n-1,j-2), j++)`). The name writes `<`, but ties occur
(`n = 2, 15, 104, 714, …`; e.g. `binomial(2,2) = binomial(1,0) = 1`) and the data follow the
program: with `<`, `a(2)` would be `3`, not the listed `2`. So `a(n)` is the least `j` with
`binomial(n, j) ≤ binomial(n-1, j-2)`; this reproduces every term of %S, %T, %U (Python).

A003258(n) is the number `m` with `c'(m) = G(A003231(n))`, where `A003231(n) = ⌊n(5+√5)/2⌋`,
`c'(m) = A249115(m) = ⌊m(5-√5)/2⌋` (its Beatty complement, strictly increasing, so `m` is
unique), and `G` is Hofstadter's G-sequence A005206: `G(0) = 0`, `G(k) = k - G(G(k-1))`. The
recursion determines `G` (by induction `G(k) ≤ k`), so we quantify over any `G` satisfying it.
(This definition reproduces the listed terms of A003258, checked in Python.)

Conjecture (Ralf Stephan, Feb 24 2004): `a(n) = A003258(n) - n + 1` for `n ≥ 1`, i.e.
`A003258(n) = a(n) + n - 1`, i.e. `c'(a(n) + n - 1) = G(A003231(n))`.
Checked in Python (exact integer arithmetic) for `1 ≤ n < 1500`.
-/

namespace OMA.S_oeis_a078489

/-- `binomial(n-1, j-2)`, which is `0` for `j < 2`. -/
def B (n j : ℕ) : ℕ := if 2 ≤ j then Nat.choose (n - 1) (j - 2) else 0

/-- A078489: the least `j` with `binomial(n, j) ≤ binomial(n-1, j-2)` (the set is nonempty:
`j = n + 1` gives `binomial(n, n+1) = 0`). -/
noncomputable def a (n : ℕ) : ℕ := sInf {j : ℕ | Nat.choose n j ≤ B n j}

/-- A003231. -/
noncomputable def A003231 (n : ℕ) : ℕ := ⌊(n : ℝ) * (5 + Real.sqrt 5) / 2⌋₊

/-- A249115, `c'`. -/
noncomputable def A249115 (m : ℕ) : ℕ := ⌊(m : ℝ) * (5 - Real.sqrt 5) / 2⌋₊

theorem main : ∀ G : ℕ → ℕ, G 0 = 0 → (∀ k : ℕ, 1 ≤ k → G k = k - G (G (k - 1))) →
    ∀ n : ℕ, 1 ≤ n → A249115 (a n + n - 1) = G (A003231 n) := by
  sorry

end OMA.S_oeis_a078489
