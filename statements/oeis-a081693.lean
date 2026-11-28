import Mathlib

/-!
# A081693: the B-sequence of the mex construction A_n = mex{A_i, B_i}, B_n = B_{n-1} + d(d+1).

Source: https://oeis.org/A081693
Credit: @Solfanbtc

`A_n = mex{A_i, B_i : 0 ≤ i < n}` (the smallest nonnegative integer not in the set) and
`B_n = B_{n-1} + (A_n - A_{n-1})(A_n - A_{n-1} + 1)`, with `A_0 = mex ∅ = 0` and `B_0 = 0`
(the data starts `0, 2, 8, 10, …`). A081693 is `B`. `AB n` is the list of pairs
`(A_0, B_0), …, (A_n, B_n)`. The mex of `s` is at most `s.length`, so `mex` searches only
`0..s.length`.

A284683 is the fixed point `w` of the morphism `σ : 0 ↦ 01, 1 ↦ 0000`. Since `σ(0)` starts with
`0`, the words `σ^k(0)` are successive prefixes of `w`, with `|σ^k(0)| ≥ k + 1`, so
`w(i) = σ^(i+1)(0)[i]` (0-indexed). A284683 has offset 1, so `w(i)` is its term at
position `i + 1`.

Conjecture (Clark Kimberling, 2017): except for the initial `0`, A081693 is the sequence of
positions of `1` in `w`. That is, for `n ≥ 1`, `B_n` is the `n`-th position (1-indexed, in
increasing order) of a `1` in A284683. Checked with python3 for `n < 20000` (and the 43
listed terms).
-/

namespace OMA.S_oeis_a081693

/-- The mex of a list of naturals. -/
def mex (s : List ℕ) : ℕ := ((List.range (s.length + 1)).find? (fun x => !(s.contains x))).getD 0

/-- `[(A_0, B_0), …, (A_n, B_n)]`. -/
def AB : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 0)]
  | n + 1 =>
    let l := AB n
    let prev := l.getLastD (0, 0)
    let a := mex (l.map Prod.fst ++ l.map Prod.snd)
    l ++ [(a, prev.2 + (a - prev.1) * (a - prev.1 + 1))]

/-- A081693(n) = B_n. -/
def B (n : ℕ) : ℕ := ((AB n).getLastD (0, 0)).2

/-- The morphism `0 ↦ 01, 1 ↦ 0000` applied to a word. -/
def σ (u : List ℕ) : List ℕ := u.flatMap fun c => if c = 0 then [0, 1] else [0, 0, 0, 0]

/-- A284683 at position `i + 1`: the `i`-th letter (0-indexed) of the fixed point of `σ`. -/
def w (i : ℕ) : ℕ := (σ^[i + 1] [0]).getD i 0

/-- The conjecture: for `n ≥ 1`, `B_n` is the `n`-th position of `1` in A284683. -/
theorem main : ∀ n : ℕ, 1 ≤ n → B n = Nat.nth (fun p => 1 ≤ p ∧ w (p - 1) = 1) (n - 1) := by
  sorry

end OMA.S_oeis_a081693
