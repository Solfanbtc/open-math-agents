import Mathlib

/-!
# A072768: The RASTxx transformation of the sequence A072643.

Source: https://oeis.org/A072768
Credit: @Solfanbtc

The RASTxx transformation (as in A071673) of a sequence `s` (indexed from 0) is `R s` with
`(R s)(0) = 0` and `(R s)(n) = s(x) + s(y) + 1` for `n ≥ 1`, where `(x, y)` is the `(n-1)`-th
cell of the table `T(x, y)` read by antidiagonals in the order
`(0,0), (1,0), (0,1), (2,0), (1,1), (0,2), …` (A071673's formula
`a(n) = 1 + a(A025581(n-1)) + a(A002262(n-1))`). A071673 is the sequence `g` with `R g = g`
(`a(0) = 0`, then reading `T(x,y) = a(x) + a(y) + 1` by antidiagonals).

A072643(n) is half the binary width of the `n`-th totally balanced binary sequence (A014486,
listed in increasing order, `0` first); since there are `C_k` (Catalan) such sequences of width
`2k` and they are listed by increasing width, A072643(n) is the number of `k ≥ 1` with
`C_0 + … + C_{k-1} ≤ n` (0, 1, 2, 2, 3, 3, 3, 3, 3, 4, …).

A072768 = `R`(A072643). The entry: A072768 first differs from A071673 at `n = 37`, `R`(A072768)
at `n = 704`, "which leads to conjecture that the repeated applications of RASTxx starting from
A072643 converge towards A071673, the fixed point of RASTxx". `main` states: there is a fixed
point `g` of `R` (this characterizes A071673) and the iterates `R^k`(A072643) converge to `g`
pointwise (each term is eventually constant, equal to `g n`). Checked with python3: these
definitions reproduce the data of A072643, A072768 and A071673 and the first differences at 37
and 704. Note: `px n ≤ n` and `py n ≤ n` (checked with python3 for `n < 1000`; true since
`diag n ≤ n`), so `R^[k] s` agrees with `g` on `[0, k)` for any start `s`; the pointwise
convergence claimed in the entry therefore holds by a simple induction. It is stated here exactly
as the entry states it, as a conjecture.
-/

namespace OMA.S_oeis_a072768

/-- The antidiagonal of index `m`: the largest `d` with `d(d+1)/2 ≤ m`. -/
def diag (m : ℕ) : ℕ := (Nat.sqrt (8 * m + 1) - 1) / 2

/-- Second coordinate of the `m`-th antidiagonal cell. -/
def py (m : ℕ) : ℕ := m - diag m * (diag m + 1) / 2

/-- First coordinate of the `m`-th antidiagonal cell. -/
def px (m : ℕ) : ℕ := diag m - py m

/-- The RASTxx transformation. -/
def R (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => s (px n) + s (py n) + 1

/-- A072643. -/
def s0 (n : ℕ) : ℕ :=
  ((Finset.range (n + 2)).filter
    (fun k => 1 ≤ k ∧ ∑ i ∈ Finset.range k, catalan i ≤ n)).card

/-- The conjecture: iterating RASTxx from A072643 converges pointwise to the fixed point
A071673. -/
theorem main : ∃ g : ℕ → ℕ, R g = g ∧
    ∀ n : ℕ, ∃ K : ℕ, ∀ k ≥ K, (R^[k] s0) n = g n := by
  sorry

end OMA.S_oeis_a072768
