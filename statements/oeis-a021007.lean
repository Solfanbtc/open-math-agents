import Mathlib

/-!
# A021007: twin-prime products `q_k = p(p+2)` with `q_k^2 > q_{k-i} q_{k+i}` for all `1 ≤ i ≤ k-1`

Source: https://oeis.org/A021007
Credit: @Solfanbtc

Let `q_k = p(p+2)` be the product of the `k`-th pair of twin primes `(p, p+2)`
((3,5), (5,7), (11,13), ...). A021007 lists the values `p + 2` such that
`q_k^2 > q_{k-i} q_{k+i}` for all `1 ≤ i ≤ k-1`: 5, 13, 31, 61, 103, ...

Remark (Robert Israel, Apr 02 2014): "Even if there are infinitely many twin primes, it is not
clear that this sequence is infinite. The Hardy-Littlewood conjecture implies that there are
infinitely many twin primes where p+2 is not in the sequence."
The first sentence is not a conjecture; we state the second one, an implication.

Reading of "the Hardy-Littlewood conjecture": the first Hardy–Littlewood (prime k-tuples)
conjecture, in its usual quantitative form: for distinct offsets `0 = m₀, m₁, ..., m_k` forming an
admissible pattern (for no prime `q` do the `m_i` cover every residue class mod `q`), the number of
`p ≤ n` with all `p + m_i` prime is asymptotic to
`C_m ∫_2^n dt / log^{k+1} t`, with `C_m = ∏_{q prime} (1 - w(q)/q) / (1 - 1/q)^{k+1}`,
`w(q)` the number of residues mod `q` among the `m_i`. (The twin-prime case `k = 1` alone,
`π₂(n) ~ 2 C₂ ∫ dt/log² t`, says nothing about the local spacing of twin pairs, which is what
the remark needs, e.g. infinitely many prime quadruplets `p, p+2, p+6, p+8`.)

Indexing: we index twin pairs from `0` (`t 0 = 3`), so the `k`-th pair of the source is
`t (k - 1)`, and the source condition `1 ≤ i ≤ k - 1` becomes `1 ≤ i ≤ j` for `j = k - 1`.

Sanity check (python): `InSeq` below, applied to the twin primes below 200000, reproduces all 46
listed terms.
-/

namespace OMA.S_oeis_a021007

open Filter Asymptotics

/-- `t j`: the smaller member of the `j`-th twin-prime pair, indexed from `0` (`t 0 = 3`). -/
noncomputable def t (j : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ (p + 2).Prime) j

/-- `q j = t j * (t j + 2)`. -/
noncomputable def q (j : ℕ) : ℕ := t j * (t j + 2)

/-- `t j + 2` belongs to A021007: `q_j^2 > q_{j-i} q_{j+i}` for all `1 ≤ i ≤ j`. -/
def InSeq (j : ℕ) : Prop := ∀ i, 1 ≤ i → i ≤ j → q (j - i) * q (j + i) < q j ^ 2

/-- An admissible pattern: for no prime `r` do the offsets cover all residues mod `r`. -/
def Admissible {k : ℕ} (m : Fin (k + 1) → ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → ¬ Function.Surjective (fun i => (m i : ZMod r))

/-- `w(r)`: the number of residue classes mod `r` among the offsets. -/
noncomputable def numResidues {k : ℕ} (r : ℕ) (m : Fin (k + 1) → ℕ) : ℕ :=
  (Set.range (fun i => (m i : ZMod r))).ncard

/-- The number of `p ≤ n` such that every `p + m i` is prime. -/
def tupleCount {k : ℕ} (m : Fin (k + 1) → ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => ∀ i, (p + m i).Prime)).card

/-- The Hardy–Littlewood singular series `C_m = ∏_{r prime} (1 - w(r)/r) / (1 - 1/r)^{k+1}`. -/
noncomputable def hlConstant {k : ℕ} (m : Fin (k + 1) → ℕ) : ℝ :=
  ∏' r : {r : ℕ // r.Prime},
    (1 - (numResidues r.1 m : ℝ) / r.1) / (1 - 1 / (r.1 : ℝ)) ^ (k + 1)

/-- The first Hardy–Littlewood (prime k-tuples) conjecture, for every admissible pattern of
distinct offsets starting at `0`. -/
def FirstHardyLittlewood : Prop :=
  ∀ (k : ℕ) (m : Fin (k + 1) → ℕ), m 0 = 0 → Function.Injective m → Admissible m →
    (fun n : ℕ => (tupleCount m n : ℝ)) ~[atTop]
      fun n : ℕ => hlConstant m * ∫ x in (2 : ℝ)..n, 1 / Real.log x ^ (k + 1)

/-- Israel's remark: the Hardy–Littlewood conjecture implies that there are infinitely many twin
primes `(p, p+2)` with `p + 2` not in A021007. -/
theorem main : FirstHardyLittlewood →
    Set.Infinite {p : ℕ | ∃ j, t j = p ∧ p.Prime ∧ (p + 2).Prime ∧ ¬ InSeq j} := by
  sorry

end OMA.S_oeis_a021007
