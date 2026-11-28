import Mathlib

/-!
# A073842: smallest unused root of n, else smallest unused power of n, never n itself.

Source: https://oeis.org/A073842
Credit: @Solfanbtc

`a(1) = 1`; for `n > 1`, `a(n)` is the smallest positive integer root of `n` (an `r` with
`r^k = n` for some `k`) not among `a(1), …, a(n-1)`, if such a root exists, otherwise the
smallest power of `n` not among `a(1), …, a(n-1)`, always subject to `a(n) ≠ n`.
A root `r ≠ n` of `n > 1` satisfies `2 ≤ r < n` and `r^k = n` with `k ≤ n`, and a power `≠ n` is
`n^(k+2)` (`k ≥ 0`). Among the `n + 2` distinct powers `n^2, …, n^(n+3)`, at least one is not
among the `n - 1` earlier terms, so the bounded searches in `step` always succeed and agree with
the unbounded definition. `L n` is the list `[a(1), …, a(n)]`.

The entry conjectures (Amarnath Murthy, 2002) that the sequence is a rearrangement of the
positive integers. This is solved: Franklin T. Adams-Watters (Jul 31 2006, formula and comment
in the entry) showed that writing `n = m^(2^k)` with `m` not a square gives
`a(n) = m^(2^(k+1))` for even `k` and `a(n) = m^(2^(k-1))` for odd `k`, so `a` is a self-inverse
permutation of the positive integers. `main` states the rearrangement claim as a bijection from
`{n ≥ 1}` onto itself. Checked with python3: the definition reproduces the 52 listed terms and
agrees with the Adams-Watters formula for `n < 400`.
-/

namespace OMA.S_oeis_a073842

/-- The term for index `n > 1`, given the earlier terms `prev`. -/
def step (prev : List ℕ) (n : ℕ) : ℕ :=
  match (List.range n).find? (fun r =>
      decide (2 ≤ r) && (List.range (n + 1)).any (fun k => r ^ k == n) && !(prev.contains r)) with
  | some r => r
  | none =>
    match ((List.range (n + 2)).map (fun k => n ^ (k + 2))).find? (fun m => !(prev.contains m)) with
    | some m => m
    | none => 0

/-- `L n = [a(1), …, a(n)]`. -/
def L : ℕ → List ℕ
  | 0 => []
  | n + 1 => L n ++ [if n = 0 then 1 else step (L n) (n + 1)]

/-- A073842(n), for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := (L n).getLastD 0

/-- The (solved) conjecture: `a` is a rearrangement of the positive integers. -/
theorem main : Set.BijOn a (Set.Ici 1) (Set.Ici 1) := by
  sorry

end OMA.S_oeis_a073842
