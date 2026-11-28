import Mathlib

/-!
# A140717: Triangle read by rows: T(n,k) is the number of Dyck paths d of semilength n such that sum of peakheights of d - number of peaks of d = k (n >= 0, 0 <= k <= floor(n^2/4)).

Source: https://oeis.org/A140717 (and A227309, A227543)
Credit: @Solfanbtc

Conjectures (Mikhail Kurkov, Aug 30 2024):
1. The antidiagonal sums `Σ_{k=0..n} T(n-k, k)` equal A227309(n), whose g.f. is
   `1/(1 - q/(1 - q^2/(1 - q^2/(1 - q^3/(1 - q^3/(1 - ...))))))`.
2. For `n > 0` the `n`-th row polynomial `Σ_k T(n,k) z^k` equals `t_n`, computed as follows:
   start with a vector `v` of fixed length `m` with `v_i = 1`, set `t = v`, and for
   `i = 1..m-1`, for `j = i+1..m`, apply simultaneously
   `[v_i, v_j] := [v_i + z^(j-i) v_j, z v_i + v_j]`, and after each cycle over `j` set
   `t_(i+1) := v_(i+1)`.
3. With `z^(j-i)` replaced by `z^(2(j-i))`, `t_n` is the `n`-th row polynomial of A227543.

Conventions.
* Dyck paths of semilength `n`: words `w : Fin (2n) → Bool` (`true = U`, `false = D`) whose
  height (U's minus D's among the first `i` steps) is `≥ 0` for all `i` and `0` at the end.
  A peak is a position `i` with `w i = U`, `w (i+1) = D`; its height is the height after step
  `i`. `stat w = Σ_peaks (height - 1)` (sum of peak heights minus number of peaks).
* Kurkov's vector is 0-indexed here (`v 0, ..., v (m-1)`), so his `t_n` is `t (n-1)`; the
  claim is stated for every length `m` and every `1 ≤ n ≤ m` (`t_n` only makes sense for
  `n ≤ m`); `mult = 1` is conjecture 2, `mult = 2` conjecture 3. Equality of row polynomials
  is stated coefficientwise.
* A227309(n) is the coefficient of `q^n` of the continued fraction truncated at depth `n+1`
  (the numerators are `q^(⌊k/2⌋+1)`, `k = 1, 2, ...`; deeper levels only change coefficients
  of order `> n`), computed in `ℚ⟦q⟧`.
* A227543 is defined by `A(x,q) = 1 + x A(qx,q) A(x,q)`; taking the coefficient of
  `x^(n+1)` gives its row polynomials `R(0) = 1`, `R(n+1) = Σ_{k=0..n} q^k R(k) R(n-k)`.
Checked (python3): the Dyck counts give the data rows `n ≤ 8`; conjecture 1 for `n < 9`
(`1, 1, 1, 2, 3, 6, 10, 19, 34`); conjectures 2 and 3 for all `1 ≤ n ≤ m ≤ 8`.
-/

namespace OMA.S_oeis_a140717

open Polynomial

/-- Height after the first `i` steps (`true = U = +1`, `false = D = -1`). -/
def height {L : ℕ} (w : Fin L → Bool) (i : ℕ) : ℤ :=
  ∑ j : Fin L, if (j : ℕ) < i then (if w j then 1 else -1) else 0

/-- `w` is a Dyck path of semilength `n`. -/
def IsDyck {n : ℕ} (w : Fin (2 * n) → Bool) : Prop :=
  (∀ i ≤ 2 * n, 0 ≤ height w i) ∧ height w (2 * n) = 0

/-- Sum of peak heights minus number of peaks. -/
def stat {L : ℕ} (w : Fin L → Bool) : ℤ :=
  ∑ i : Fin L, ∑ j : Fin L,
    if (j : ℕ) = i + 1 ∧ w i = true ∧ w j = false then height w (i + 1) - 1 else 0

/-- A140717: `T(n,k)`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin (2 * n) → Bool | IsDyck w ∧ stat w = k}

/-- One simultaneous update `[v_i, v_j] := [v_i + z^(mult (j-i)) v_j, z v_i + v_j]`. -/
noncomputable def pairStep (mult i j : ℕ) (v : ℕ → ℤ[X]) : ℕ → ℤ[X] :=
  Function.update (Function.update v i (v i + X ^ (mult * (j - i)) * v j)) j (X * v i + v j)

/-- The cycle over `j = i+1, ..., m-1` (0-indexed). -/
noncomputable def cycle (mult m i : ℕ) (v : ℕ → ℤ[X]) : ℕ → ℤ[X] :=
  (List.range' (i + 1) (m - (i + 1))).foldl (fun v j => pairStep mult i j v) v

/-- Kurkov's procedure on a vector of length `m`; returns `(v, t)`. -/
noncomputable def run (mult m : ℕ) : (ℕ → ℤ[X]) × (ℕ → ℤ[X]) :=
  (List.range (m - 1)).foldl
    (fun s i => (cycle mult m i s.1, Function.update s.2 (i + 1) (cycle mult m i s.1 (i + 1))))
    (fun _ => 1, fun _ => 1)

/-- Kurkov's `t_n` (1-indexed) for a vector of length `m`. -/
noncomputable def kurkovT (mult m n : ℕ) : ℤ[X] := (run mult m).2 (n - 1)

/-- Truncated continued fraction `1 - q^(⌊k/2⌋+1)/(1 - q^(⌊(k+1)/2⌋+1)/(...))`, `d` levels. -/
noncomputable def cf : ℕ → ℕ → PowerSeries ℚ
  | _, 0 => 1
  | k, d + 1 => 1 - PowerSeries.X ^ (k / 2 + 1) * (cf (k + 1) d)⁻¹

/-- A227309(n). -/
noncomputable def A227309 (n : ℕ) : ℚ := PowerSeries.coeff n (cf 1 (n + 1))⁻¹

/-- Row polynomials of A227543: `R(n+1) = Σ_{k=0..n} q^k R(k) R(n-k)`. -/
noncomputable def R : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), X ^ (k : ℕ) * R k * R (n - k)
decreasing_by all_goals omega

/-- Kurkov's three conjectures for A140717. -/
theorem main :
    (∀ n : ℕ, ((∑ k ∈ Finset.range (n + 1), T (n - k) k : ℕ) : ℚ) = A227309 n) ∧
    (∀ m n : ℕ, 1 ≤ n → n ≤ m → ∀ k : ℕ, (kurkovT 1 m n).coeff k = T n k) ∧
    (∀ m n : ℕ, 1 ≤ n → n ≤ m → kurkovT 2 m n = R n) := by
  sorry

end OMA.S_oeis_a140717
