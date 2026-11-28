import Mathlib

/-!
# A005150: Look and Say sequence: describe the previous term! (method A - initial term is 1).

Source: https://oeis.org/A005150
Credit: @Solfanbtc

Conjecture (OEIS entry): $DC(a(n)) \sim k \cdot \lambda^n$, where $k$ is approximately
$1.021\ldots$, $\lambda$ is Conway's constant and $DC$ denotes the number of digit changes
in the decimal representation (e.g. $DC(13112221) = 4$ because 1->3, 3->1, 1->2, 2->1).

Conventions.
* Terms are represented by their list of decimal digits, most significant first:
  `term 1 = [1]`, `term 2 = [1, 1]`, `term 3 = [2, 1]`, `term 4 = [1, 2, 1, 1]`, ...
  (offset 1, as in the OEIS; `term 0` is a junk value that does not affect an asymptotic).
* `dc l` counts the indices `i` with `l[i] ≠ l[i+1]`.
* Conway's constant $\lambda = 1.303577\ldots$ is taken as the limit of the ratio of the
  lengths of consecutive terms (that this limit exists and equals the largest root of Conway's
  degree-71 polynomial is Conway's theorem).
* "$k$ is approximately $1.021\ldots$" is read as: the decimal expansion of $k$ begins
  $1.021$, i.e. $1.021 \le k < 1.022$. Numerically (exact digit strings up to $n = 60$)
  $DC(a(n))/\lambda^n \approx 1.0211$.

The entry states a second conjecture, that $(c_2+c_3-c_1)/(c_1+c_2+c_3)$ tends to a limit
"approximately $0.01$" ($c_i$ = number of digits $i$ in $a(n)$). It gives no precision for
"approximately", so it has no exact content to state and is not included here.
-/

namespace OMA.S_oeis_a005150

open Filter Asymptotics

/-- Run-length encoding: list of (digit, run length), in order. -/
def rle : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs =>
    match rle xs with
    | (y, c) :: rest => if x = y then (y, c + 1) :: rest else (x, 1) :: (y, c) :: rest
    | [] => [(x, 1)]

/-- One look-and-say step on a list of decimal digits: each run of `c` copies of `d`
becomes the decimal digits of `c` followed by `d`. -/
def step (l : List ℕ) : List ℕ :=
  (rle l).flatMap fun p => (Nat.digits 10 p.2).reverse ++ [p.1]

/-- The decimal digits of $a(n)$ (A005150, offset 1, $a(1) = 1$). -/
def term (n : ℕ) : List ℕ := step^[n - 1] [1]

/-- Number of digit changes: indices `i` with `l[i] ≠ l[i+1]`. -/
def dc : List ℕ → ℕ
  | x :: y :: rest => (if x ≠ y then 1 else 0) + dc (y :: rest)
  | _ => 0

/-- Conway's constant, as the limit of the ratio of lengths of consecutive terms. -/
noncomputable def conwayConstant : ℝ :=
  limUnder atTop fun n : ℕ => ((term (n + 1)).length : ℝ) / (term n).length

theorem main :
    ∃ k : ℝ, 1.021 ≤ k ∧ k < 1.022 ∧
      IsEquivalent atTop (fun n : ℕ => (dc (term n) : ℝ)) (fun n => k * conwayConstant ^ n) := by
  sorry

end OMA.S_oeis_a005150
