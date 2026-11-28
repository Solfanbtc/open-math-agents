import Mathlib

/-!
# A071356: inversion sequences and stack-sorting preimages counted by (1 - 2x - √(1-4x-4x²))/(4x²)

Source: https://oeis.org/A071356
Credit: @Solfanbtc

A071356 (offset 0): the expansion of `A(x) = (1 - 2x - sqrt(1 - 4x - 4x^2))/(4x^2)`;
data 1, 2, 6, 20, 72, 272, 1064, … Clearing the square root, `A` is the power series solution
with `A(0) = 1` of `A = 1 + 2x A + 2x^2 A^2`, i.e. `a(0) = 1` and
`a(n) = 2a(n-1) + 2 Sum_{i+j=n-2} a(i) a(j)`; we use this recurrence as the definition
(it reproduces the data).

Conjectures in the entry, all stated in `main` for every `n ≥ 0`:
* (E. M. Schmidt, 2017, citing Martinez and Savage, 2.19) "Conjecturally, the number of
  sequences (e(1), ..., e(n+1)), 0 <= e(i) < i, such that there is no triple i < j < k with
  e(i) > e(j) <= e(k)."
* (C. Defant, 2018) with `s` West's stack-sorting map and `Av_m(τ_1, …)` the permutations of
  `[m]` avoiding the patterns: "It is conjectured that a(n) = |s^{-1}(Av_{n+1}(132, 231))| =
  |s^{-1}(Av_{n+1}(132, 312))| = |s^{-1}(Av_{n+1}(231, 312))|. Only the last of these equalities
  is known." (the known one is included, as part of the chain).

Definitions. Inversion sequences are indexed from `0`: `e : Fin (n+1) → ℕ` with `e(i) ≤ i`
(i.e. `0 ≤ e(i) < i` in 1-based indexing). West's stack-sorting map reads the entries left to
right; before pushing an entry it pops (to the output) every stack entry smaller than it, and at
the end it pops the rest; this equals the recursive form `s(L m R) = s(L) s(R) m` with `m` the
maximum (checked with python3 on all permutations of size `≤ 7`). A permutation `p` contains
`132` if `p_i < p_k < p_j` for some `i < j < k`, `231` if `p_k < p_i < p_j`, `312` if
`p_j < p_k < p_i`. Checked with python3 by brute force: all four counts equal `a(n)` for
`0 ≤ n ≤ 6`.
-/

namespace OMA.S_oeis_a071356

/-- A071356 via `A = 1 + 2x A + 2x^2 A^2`. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * a n + 2 * ∑ i : Fin n, a i.val * a (n - 1 - i.val)
decreasing_by
  all_goals first
    | omega
    | (have := i.isLt; omega)

/-- The number of inversion sequences `e(0), …, e(n)` (`e(i) ≤ i`) with no `i < j < k` such that
`e(i) > e(j) ≤ e(k)`. -/
noncomputable def invCount (n : ℕ) : ℕ :=
  {e : Fin (n + 1) → ℕ | (∀ i, e i ≤ i.val) ∧
    ¬ ∃ i j k : Fin (n + 1), i < j ∧ j < k ∧ e j < e i ∧ e j ≤ e k}.ncard

/-- West's stack-sorting map, as the stack procedure. -/
def stackSort (p : List ℕ) : List ℕ :=
  let r := p.foldl (fun (st : List ℕ × List ℕ) x =>
    let sp := st.1.span (· < x)
    (x :: sp.2, st.2 ++ sp.1)) ([], [])
  r.2 ++ r.1

/-- `p` contains the pattern `132`. -/
def has132 (p : List ℕ) : Prop :=
  ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p.get i < p.get k ∧ p.get k < p.get j

/-- `p` contains the pattern `231`. -/
def has231 (p : List ℕ) : Prop :=
  ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p.get k < p.get i ∧ p.get i < p.get j

/-- `p` contains the pattern `312`. -/
def has312 (p : List ℕ) : Prop :=
  ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p.get j < p.get k ∧ p.get k < p.get i

/-- The number of permutations `π` of `[m]` such that `s(π)` satisfies `P`. -/
noncomputable def preimageCount (m : ℕ) (P : List ℕ → Prop) : ℕ :=
  {π : List ℕ | π.Perm (List.range' 1 m) ∧ P (stackSort π)}.ncard

/-- The Martinez-Savage and Defant conjectures for A071356. -/
theorem main : ∀ n : ℕ,
    invCount n = a n ∧
    preimageCount (n + 1) (fun q => ¬ has132 q ∧ ¬ has231 q) = a n ∧
    preimageCount (n + 1) (fun q => ¬ has132 q ∧ ¬ has312 q) = a n ∧
    preimageCount (n + 1) (fun q => ¬ has231 q ∧ ¬ has312 q) = a n := by
  sorry

end OMA.S_oeis_a071356
