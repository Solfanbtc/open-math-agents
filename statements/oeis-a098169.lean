import Mathlib

/-!
# A098169: a(n) = Sum_{i=1..n} A098168(i).

Source: https://oeis.org/A098169
Credit: @Solfanbtc

The `n`-th Fortunate number `A005235(n)` (`n ≥ 1`) is the least `m > 1` such that
`p_n# + m` is prime, where `p_n#` is the product of the first `n` primes.
`A098168(n)` is the prime index `j` with `prime(j) = A005235(n)`; following the entry's
Mathematica program we take it to be `π(A005235(n))` (`PrimePi[Fortunate[n]]`), which is
that index whenever the Fortunate number is prime (Fortune's conjecture, stated upstream as
`FortuneConjecture.fortune_conjecture`; it is not needed to make sense of this statement).
`A098169(n) = Σ_{i=1..n} A098168(i)` (offset 1; a(1..5) = 2, 5, 9, 15, 24, checked).

Conjecture (OEIS %F, Pierre Cami): `a(n) / triangular(n) → log(e·π/2)`,
with `triangular(n) = n(n+1)/2`.
-/

namespace OMA.S_oeis_a098169

/-- The product of the first `n` primes, `p_n#`. -/
noncomputable def primorialFirst (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- The `n`-th Fortunate number, A005235(n): the least `m > 1` with `p_n# + m` prime. -/
noncomputable def fortunate (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ (primorialFirst n + m).Prime}

/-- A098168(n) = π(A005235(n)). -/
noncomputable def A098168 (n : ℕ) : ℕ := Nat.primeCounting (fortunate n)

/-- A098169(n) = Σ_{i=1..n} A098168(i). -/
noncomputable def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, A098168 i

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1) / 2)) Filter.atTop
      (nhds (Real.log (Real.exp 1 * Real.pi / 2))) := by
  sorry

end OMA.S_oeis_a098169
