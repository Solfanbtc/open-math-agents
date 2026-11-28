import Mathlib

/-!
# A055186: Cumulative counting sequence, method A (adjective-before-noun) pairs, first term 0

Source: https://oeis.org/A055186
Credit: @Solfanbtc

Start with `0`; at each step, write down what is in the sequence so far: "how many times each
integer (in increasing order) `≤ max {existing terms}` appears in the sequence", as pairs
"count, value", and concatenate: `0; 1,0; 2,0,1,1; 3,0,3,1,1,2; …`. Every integer from `0` to the
current maximum gets a pair, also when its count is `0` (e.g. the pairs `…, 0, 7, 0, 8, …`
in the data). `seqAfter k` is the list of terms after `k` steps (`seqAfter 0 = [0]`); each is a
prefix of the next. This reproduces all 100 data terms; `a(n)` is the `n`-th term (offset 1).

Conjectures (Benoit Cloitre, Jan 28 2003, OEIS formula): `a(n) < 2√n`; and
`lim_{n→∞} max(a(k) : 1 ≤ k ≤ n)/√n` exists and equals `2`. Both are stated, as the parts of `main`.

Status: FALSE for the sequence as now defined. A direct computation gives `a(698) = 53 > 2√698 =
52.84…` (the first violation; 80205 violations below `n = 300000`), and
`max_{k ≤ n} a(k)/√n` is `2.83` at `n = 10^4` and `4.87` at `n = 3·10^5`. Cloitre's conjectures
predate a change of definition: the sequence originally listed here (values in order of first
appearance, now A217760) differs from the present one from the 62nd term on, and the entry notes
that a conjecture formerly placed here applies to A217760. The conjectures are stated faithfully,
for the sequence the entry now defines.
-/

namespace OMA.S_oeis_a055186

/-- The next segment: `count, value` for every value `0, 1, …, max l`. -/
def segment (l : List ℕ) : List ℕ :=
  (List.range (l.foldl max 0 + 1)).flatMap fun v => [l.count v, v]

/-- The terms after `k` steps. -/
def seqAfter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => seqAfter k ++ segment (seqAfter k)

/-- A055186 (offset 1): `a(n)` is the `n`-th term (`seqAfter n` has more than `n` terms). -/
def a (n : ℕ) : ℕ := (seqAfter n).getD (n - 1) 0

/-- Cloitre's conjectures (false for the present definition, see the module docstring). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) < 2 * Real.sqrt n) ∧
    Filter.Tendsto (fun n : ℕ =>
      (((Finset.Icc 1 n).sup a : ℕ) : ℝ) / Real.sqrt n) Filter.atTop (nhds 2) := by
  sorry

end OMA.S_oeis_a055186
