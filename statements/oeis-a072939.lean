import Mathlib

/-!
# A072939: Define a sequence c depending on n as follows: c(1)=1 and c(2)=n; c(k+2) = (c(k+1) + c(k))/2 if c(k+1) and c(k) have the same parity; otherwise c(k+2) = abs(c(k+1) - 2*c(k)); sequence gives values of n such that lim_{k->oo} c(k) = infinity.

Source: https://oeis.org/A072939
Credit: @Solfanbtc

For `n ≥ 1`, `c(1) = 1`, `c(2) = n`, `c(k+2) = (c(k+1) + c(k))/2` when `c(k+1)`, `c(k)` have the
same parity (the sum is then even), otherwise `c(k+2) = |c(k+1) - 2 c(k)|`. A072939 is the
increasing list of the `n ≥ 1` with `c(k) → ∞`. (Below `c` is 0-indexed: `cseq n k = c(k+1)`.)
The terms `3, 7, 9, …, 179` of %S, %T, %U are reproduced by simulation in Python.

Conjectures in the entry:
1. (Vladeta Jovovic, 2003) `a(n) = A036554(n) + 1`, where A036554 lists the positive integers
   whose binary expansion ends in an odd number of zeros (odd 2-adic valuation). Both sides are
   increasing enumerations, so this says: `c(k) → ∞` iff `n - 1 ≥ 1` and `v₂(n - 1)` is odd.
2. (Clark Kimberling, 2017) A072939 gives the positions of the 0's in A285384, the limiting
   1-word of the morphism `σ : 0 ↦ 11, 1 ↦ 01` (the entry's comment writes `1 -> 10`; the name of
   A285384 was later corrected to `1 -> 01`, and A285384 is what the conjecture refers to). The
   even iterates `σ^(2j)(1)` are prefixes of each other and of A285384 (`σ²(1) = 1101` starts
   with `1`), and have length `4^j ≥ j`, so A285384(j) is entry `j - 1` of `σ^(2j)(1)`.
3. (N. J. A. Sloane, 2019) A072939 gives the positions of the 1's in A328979, the trajectory of
   `0` under `0 ↦ 0010, 1 ↦ 1010`; A328979(j) is entry `j - 1` of the `j`-th iterate from `0`.
4. (formula) `a(n)/n → 3`.
All four were checked in Python for `n < 3000` (`n = 2049` grows slowly: `c(k) ≈ k/2`).
Positions of words are 1-indexed, as in the OEIS.
-/

namespace OMA.S_oeis_a072939

/-- `cseq n k = c(k+1)`: `c(1) = 1`, `c(2) = n`. -/
def cseq (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => n
  | k + 2 =>
    if cseq n (k + 1) % 2 = cseq n k % 2 then (cseq n (k + 1) + cseq n k) / 2
    else ((cseq n (k + 1) : ℤ) - 2 * cseq n k).natAbs

/-- The set of terms of A072939. -/
def S : Set ℕ := {n | 1 ≤ n ∧ Filter.Tendsto (cseq n) Filter.atTop Filter.atTop}

/-- Apply a morphism `f` letter by letter. -/
def morph (f : ℕ → List ℕ) (w : List ℕ) : List ℕ := w.flatMap f

/-- A285384(j), `j ≥ 1`: limiting 1-word of `0 ↦ 11, 1 ↦ 01`. -/
def A285384 (j : ℕ) : ℕ :=
  ((morph (fun x => if x = 0 then [1, 1] else [0, 1]))^[2 * j] [1]).getD (j - 1) 0

/-- A328979(j), `j ≥ 1`: trajectory of `0` under `0 ↦ 0010, 1 ↦ 1010`. -/
def A328979 (j : ℕ) : ℕ :=
  ((morph (fun x => if x = 0 then [0, 0, 1, 0] else [1, 0, 1, 0]))^[j] [0]).getD (j - 1) 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → (n ∈ S ↔ 1 ≤ n - 1 ∧ Odd (padicValNat 2 (n - 1)))) ∧
    (∀ n : ℕ, 1 ≤ n → (n ∈ S ↔ A285384 n = 0)) ∧
    (∀ n : ℕ, 1 ≤ n → (n ∈ S ↔ A328979 n = 1)) ∧
    Filter.Tendsto (fun n : ℕ => (Nat.nth (· ∈ S) (n - 1) : ℝ) / n) Filter.atTop (nhds 3) := by
  sorry

end OMA.S_oeis_a072939
