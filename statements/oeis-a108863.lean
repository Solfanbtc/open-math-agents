import Mathlib

/-!
# A108863: Number of Dyck paths containing exactly one UUUD.

Source: https://oeis.org/A108863
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Dec 11 2008): "this is the Motzkin transform of the sequence of three
zeros followed by A001651."

Definitions.
* A Dyck path of semilength `n` is a word of length `2n` in U (`true`) and D (`false`) whose
  prefixes never have more D than U and with as many U as D. `a n` counts those in which the
  factor UUUD occurs exactly once (as a block of 4 consecutive steps). This gives
  0, 0, 0, 1, 5, 21, 78, 274 for n = 0..7 (`#eval`), the data.
* `b` is the sequence 0, 0, 0 followed by A001651 (numbers not divisible by 3:
  1, 2, 4, 5, 7, 8, ...; A001651(m) = (3m - 2 + (m mod 2))/2), indexed from 0.
* Motzkin transform. The entry does not define it; we use the meaning in which R. J. Mathar
  uses it in OEIS comments: the Motzkin transform of `b` is the sequence with generating
  function `B(x M(x))`, where `B` is the g.f. of `b` and `M(x) = Sum_n M_n x^n` the g.f. of the
  Motzkin numbers A001006 (M_n = Sum_k C(n, 2k) Catalan(k)). With this reading the
  transform reproduces all 28 data terms (python3), while the variant `M(x) B(x M(x))` already
  fails at n = 4. Since `(x M(x))^k` has no term below degree `k`, the n-th coefficient of
  `B(x M(x))` is `Sum_{k ≤ n} b k * [x^n] (x M(x))^k`.
* Statement: for every `n`, `a n` equals that coefficient.
-/

namespace OMA.S_oeis_a108863

/-- `w` (true = U, false = D) is a Dyck path. -/
def IsDyck (w : List Bool) : Prop :=
  (∀ i ≤ w.length, (w.take i).count false ≤ (w.take i).count true) ∧
    w.count false = w.count true

instance : DecidablePred IsDyck := fun w => by unfold IsDyck; infer_instance

/-- Number of positions where the factor UUUD starts. -/
def countUUUD (w : List Bool) : ℕ :=
  ((List.range w.length).filter fun i => (w.drop i).take 4 = [true, true, true, false]).length

/-- A108863(n): Dyck paths of semilength `n` with exactly one UUUD. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n) → Bool)).filter fun f =>
    IsDyck (List.ofFn f) ∧ countUUUD (List.ofFn f) = 1).card

/-- Motzkin numbers A001006. -/
def motzkin (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * catalan k

/-- Three zeros followed by A001651 (offset 0). -/
def b (k : ℕ) : ℕ := if k < 3 then 0 else (3 * (k - 2) - 2 + (k - 2) % 2) / 2

/-- The `n`-th coefficient of the Motzkin transform `B(x M(x))` of `b`. -/
noncomputable def motzkinTransform (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    b k * PowerSeries.coeff n ((PowerSeries.X * PowerSeries.mk motzkin) ^ k)

theorem main : ∀ n : ℕ, a n = motzkinTransform n := by
  sorry

end OMA.S_oeis_a108863
