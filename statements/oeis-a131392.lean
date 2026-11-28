import Mathlib

/-!
# A131392: Positions of negative integers in A131389, minus 1.

Source: https://oeis.org/A131392
Credit: @Solfanbtc

Claim (OEIS A131392 and A131391, %C lines): if A131389 is a permutation of the integers, as
conjectured (Clark Kimberling, A131389 and A131388), then A131392 is the complement of A131391.

Definitions (Kimberling's Rule 1, A131388). Start with `k = 1`, `a(1) = 1`, `d(1) = 0`, and let
`A(k) = {a(1), ..., a(k)}`, `D(k) = {d(1), ..., d(k)}`.
* Step 1: if some integer `h` with `1 - a(k) < h < 0` has `h ∉ D(k)` and `a(k) + h ∉ A(k)`,
  let `d(k+1)` be the greatest such `h` and `a(k+1) = a(k) + h`;
* Step 2: otherwise let `h` be the least positive integer with `h ∉ D(k)` and `a(k) + h ∉ A(k)`,
  and `a(k+1) = a(k) + h`, `d(k+1) = h`.
A131388 is `(a(k))`, A131389 is `(d(k))`. A131391 (resp. A131392) lists, increasingly, the
numbers `k - 1` for the positions `k` where `d(k)` is positive (resp. negative).

Formalization.
* `step l` computes the next pair `(a(k+1), d(k+1))` from `l = [(a(1), d(1)), ..., (a(k), d(k))]`.
  Step 1 scans `h = -1, -2, ..., -a(k)`, first hit = greatest. In Step 2 the least `h` is at most
  `2k + 1` (at most `2k` positive values are excluded by `D(k)` and `A(k) - a(k)`), so the
  bounded search over `1, ..., 2k + 2` finds it and the fallback `0` is never used.
* "A131389 is a permutation of the integers": every integer is `d(k)` for exactly one `k ≥ 1`.
* "A131392 is the complement of A131391": as subsets of the positive integers,
  `{n ≥ 1 | d(n+1) < 0} = {n ≥ 1} \ {n ≥ 1 | d(n+1) > 0}`.

Status: elementary as stated; each `d(k)`, `k ≥ 2`, is nonzero (Step 1 gives `h < 0`, Step 2
`h > 0`), so the conclusion even holds without the hypothesis. The hypothesis is the open
conjecture of A131389. Stated as posed.

Checked with python3: Rule 1 reproduces all listed terms of A131388, A131389, A131391 and A131392.
-/

namespace OMA.S_oeis_a131392

/-- One step of Rule 1, from the list of pairs `(a(i), d(i))`, `i ≤ k`. -/
def step (l : List (ℤ × ℤ)) : ℤ × ℤ :=
  let ak := (l.getLast?.map Prod.fst).getD 0
  let As := l.map Prod.fst
  let Ds := l.map Prod.snd
  let negs := ((List.range ak.toNat).map (fun i => -((i : ℤ) + 1))).filter
    (fun h => decide (1 - ak < h) && !(Ds.contains h) && !(As.contains (ak + h)))
  match negs.head? with
  | some h => (ak + h, h)
  | none =>
    let h := (((List.range (2 * l.length + 2)).map (fun i => (i : ℤ) + 1)).find?
      (fun h => !(Ds.contains h) && !(As.contains (ak + h)))).getD 0
    (ak + h, h)

/-- `gen k = [(a(1), d(1)), ..., (a(k+1), d(k+1))]`. -/
def gen : ℕ → List (ℤ × ℤ)
  | 0 => [(1, 0)]
  | k + 1 => gen k ++ [step (gen k)]

/-- A131389: `d(k)` for `k ≥ 1`. -/
def d (k : ℕ) : ℤ := ((gen (k - 1)).getD (k - 1) (0, 0)).2

/-- A131391 as a set: `k - 1` for the positions `k` of positive terms of A131389. -/
def A131391 : Set ℕ := {n | 1 ≤ n ∧ 0 < d (n + 1)}

/-- A131392 as a set: `k - 1` for the positions `k` of negative terms of A131389. -/
def A131392 : Set ℕ := {n | 1 ≤ n ∧ d (n + 1) < 0}

/-- If A131389 is a permutation of the integers, then A131392 is the complement of A131391 in
the positive integers. -/
theorem main : (∀ z : ℤ, ∃! k : ℕ, 1 ≤ k ∧ d k = z) → A131392 = {n | 1 ≤ n} \ A131391 := by
  sorry

end OMA.S_oeis_a131392
