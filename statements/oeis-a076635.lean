import Mathlib

/-!
# A076635: Let b(1)=1/n, b(2)=1, b(k+1)=abs(b(k))-b(k-1)^2; then b(k) is >0 for k>a(n).

Source: https://oeis.org/A076635
Credit: @Solfanbtc

The entry contains two conjectures (Benoit Cloitre, 2002):
* %F: "a(n) seems to be asymptotic to c*log(n) with c=5.63..." This is the statement below.
* %C: "lim_{k->infinity} (b(k)-k)/log(k) = f(n), constant depending on n". Taken literally this is
  false for every `n`: `b(k) → 0` (numerically `b(k) ≈ 1/k`), so `(b(k)-k)/log(k) → -∞`. The
  quoted values `f(2) = 2.9…`, `f(5) = 2.25…` match `(1/b(k) - k)/log(k)` at `k ≈ 10^3 … 10^4`,
  so `1/b(k)` was probably meant; we do not state this guessed reading. (Heuristically
  `1/b(k+1) ≈ 1/b(k) + 1 + 3 b(k)`, which suggests the limit is `3` for every `n`.)

Conventions:
* Offset 2: `n ≥ 2`. `b(1) = 1/n`, `b(2) = 1`, `b(k+1) = |b(k)| - b(k-1)^2` for `k ≥ 2`, in `ℝ`
  (all values are rational). In Lean `b n k` is `b(k)` with the same indexing (`b n 0` is an
  unused filler).
* `a(n)` is the least `m` such that `b(k) > 0` for all `k > m` (example: `a(5) = 11`, as
  `b(11) < 0`). Checked in Python with 200-digit decimals: this reproduces all 66 listed terms.
* "c = 5.63..." is read as `5.63 ≤ c < 5.64`; `~` is `Asymptotics.IsEquivalent` as `n → ∞`.
  Numerically `a(n)/log(n)` is `5.94, 5.75, 5.65` at `n = 10^3, 10^4, 10^5`.
-/

namespace OMA.S_oeis_a076635

open Filter Asymptotics

/-- `b n k` is `b(k)` for the parameter `n`: `b(1) = 1/n`, `b(2) = 1`,
`b(k+1) = |b(k)| - b(k-1)^2`. -/
noncomputable def b (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / (n : ℝ)
  | 2 => 1
  | k + 3 => |b n (k + 2)| - (b n (k + 1)) ^ 2

/-- `a(n)`: the least `m` such that `b(k) > 0` for every `k > m`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ∀ k, m < k → 0 < b n k}

/-- Cloitre's conjecture: `a(n) ~ c log n` with `c = 5.63…`. -/
theorem main : ∃ c : ℝ, 5.63 ≤ c ∧ c < 5.64 ∧
    IsEquivalent atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => c * Real.log n) := by
  sorry

end OMA.S_oeis_a076635
