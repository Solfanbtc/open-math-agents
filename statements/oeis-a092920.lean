import Mathlib

/-!
# A092920: Number of strongly monotone partitions of [n].

Source: https://oeis.org/A092920
Credit: @Solfanbtc

A set partition is strongly monotone if its blocks can be written in increasing order of
their least elements and of their greatest elements simultaneously, i.e. for distinct blocks
`B, C`: `min B < min C → max B < max C`. `a(n)` counts strongly monotone partitions of an
`n`-element ordered set, here `{0, ..., n-1}` (`a(0) = 1`, the empty partition).

Conjecture (Mikhail Kurkov, Apr 24 2023, OEIS %F): `a(n) = Σ_{k=0}^{2^(n-1)-1} b(k)` for
`n > 0`, where `b(0) = 1` and for `m, n ≥ 0`
`b(2^m (2n+1)) = Σ_{k=0}^{[m>0](m-1)} binomial(m-1, k) b(2^k n)`.
For `m = 0` the sum has the single term `k = 0` with `binomial(-1, 0) = 1`, so `b(2n+1) = b(n)`.
For `m ≥ 1` it is `Σ_{k=0}^{m-1} binomial(m-1, k) b(2^k n)`.

`b` is computed with fuel: every recursive call strictly decreases the argument
(`n < 2n+1` and `2^k n < 2^m (2n+1)` for `k < m`), so fuel `N + 1` suffices for `b N`.
Checked in Python: the conjectured formula and a brute-force count of strongly monotone
partitions both reproduce the data (`n ≤ 16` and `n ≤ 8` respectively).
-/

namespace OMA.S_oeis_a092920

/-- Strongly monotone: for distinct blocks, smaller least element implies smaller greatest
element. -/
def StronglyMonotone {n : ℕ} (P : Finpartition (Finset.range n)) : Prop :=
  ∀ B ∈ P.parts, ∀ C ∈ P.parts, B ≠ C → B.min < C.min → B.max < C.max

/-- A092920(n): the number of strongly monotone partitions of `{0, ..., n-1}`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun P : Finpartition (Finset.range n) => StronglyMonotone P)).card

/-- Kurkov's auxiliary sequence `b`, with fuel. -/
def bAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, N =>
    if N = 0 then 1 else
      let m := padicValNat 2 N
      let n := N / 2 ^ m / 2
      if m = 0 then bAux f n
      else ∑ k ∈ Finset.range m, (m - 1).choose k * bAux f (2 ^ k * n)

/-- `b N`. -/
def b (N : ℕ) : ℕ := bAux (N + 1) N

theorem main : ∀ n : ℕ, 0 < n → a n = ∑ k ∈ Finset.range (2 ^ (n - 1)), b k := by
  sorry

end OMA.S_oeis_a092920
