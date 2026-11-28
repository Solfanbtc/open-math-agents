import Mathlib

/-!
# A007413: A squarefree (or Thue-Morse) ternary sequence: closed under 1->123, 2->13, 3->2. Start with 1.

Source: https://oeis.org/A007413
Credit: @Solfanbtc

`a = A007413` (offset 1) is the fixed point starting with 1 of the morphism
`1 ↦ 123, 2 ↦ 13, 3 ↦ 2`: `1, 2, 3, 1, 3, 2, 1, 2, 3, 2, ...`.

`b = A076826` (offset 0): `b(n) = 2 (∑_{k=0}^{n} t(k)) - n`, with `t = A010060` the Thue–Morse
sequence (`t(k)` = parity of the number of 1's in the binary expansion of `k`):
`0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, ...`.

Conjecture (Vladimir Shevelev, May 31 2009, in the entry): the sequence `a` is formed by the
numbers of 1's between every pair of consecutive 2's in `b`. Stated as: if `p₀ < p₁ < ...` are the
positions of the 2's in `b`, then for every `n ≥ 1`, `a(n)` is the number of `i` with
`p_{n-1} < i < p_n` and `b(i) = 1`.

A python3 check: true for the first 49999 gaps (all 2's of `b` below `2·10⁵`). The Lean kernel
(`decide`) confirms the first 12 terms of `a` and of `b` against the data.

Conventions:
* `w k` is the `k`-th iterate of the morphism on `[1]`; each `w k` is a prefix of `w (k+1)`, and
  `|w k| ≥ k + 1`, so `a(n) = (w n)[n - 1]`.
* `b` takes values in `ℤ`; `p j = Nat.nth (fun i => b i = 2) j` (there are infinitely many 2's).
-/

namespace OMA.S_oeis_a007413

/-- The morphism `1 ↦ 123, 2 ↦ 13, 3 ↦ 2`. -/
def σ : ℕ → List ℕ
  | 1 => [1, 2, 3]
  | 2 => [1, 3]
  | 3 => [2]
  | _ => []

/-- `w k = σ^k([1])`. -/
def w : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => (w k).flatMap σ

/-- `a n = A007413(n)` (`n ≥ 1`). -/
def a (n : ℕ) : ℕ := (w n).getD (n - 1) 0

/-- The Thue–Morse sequence A010060. -/
def t (k : ℕ) : ℕ := (Nat.digits 2 k).sum % 2

/-- `b n = A076826(n) = 2 ∑_{k ≤ n} t(k) - n`. -/
def b (n : ℕ) : ℤ := 2 * (∑ k ∈ Finset.range (n + 1), (t k : ℤ)) - n

/-- Positions of the 2's in `b`. -/
noncomputable def p (j : ℕ) : ℕ := Nat.nth (fun i => b i = 2) j

/-- Shevelev's conjecture: `a(n)` is the number of 1's of `b` strictly between its `n`-th and
`(n+1)`-th 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ((Finset.Ioo (p (n - 1)) (p n)).filter (fun i => b i = 1)).card := by
  sorry

end OMA.S_oeis_a007413
