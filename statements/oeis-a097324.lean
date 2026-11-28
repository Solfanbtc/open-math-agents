import Mathlib

/-!
# A097324: Numbers n such that A067655(n) is different from A049606(n).

Source: https://oeis.org/A097324
Credit: @Solfanbtc

Equivalently (entry comment): the denominator of 2^n/n! differs from the denominator of
sum(k=1, n, C(n-1,k-1)*2^k/k!).

Conjecture (entry comment): "the sequence is infinite, the sequence and its complement (cases
where the two values are equal) equipartition N and the difference between consecutive members
of this sequence never exceeds c=7."

Formalization.
* `InSeq n` : `n ≥ 1` (offset 1; A067655 starts at n = 1) and the two reduced denominators,
  computed in `ℚ`, differ. With this, the terms below 162 are exactly the listed data
  14, 18, 23, ..., 161 (checked with python3 up to n = 1500; the largest gap there is 7).
* "infinite": `{n | InSeq n}.Infinite`.
* "equipartition N": the natural density of the sequence is 1/2.
* "consecutive members differ by at most 7": for every member `n` there is a member in
  `(n, n + 7]`.
The three parts are stated as one conjunction, as in the source. (Numerically the proportion
up to 1500 is about 0.58, so the density part may well be false; it is stated as the source
states it.)
-/

namespace OMA.S_oeis_a097324

/-- `n` is a term of A097324. -/
def InSeq (n : ℕ) : Prop :=
  1 ≤ n ∧
    ((2 : ℚ) ^ n / n.factorial).den ≠
      (∑ k ∈ Finset.Icc 1 n, ((n - 1).choose (k - 1) : ℚ) * 2 ^ k / k.factorial).den

instance : DecidablePred InSeq := fun n => by unfold InSeq; infer_instance

theorem main :
    {n : ℕ | InSeq n}.Infinite ∧
    Filter.Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter InSeq).card : ℝ) / N)
      Filter.atTop (nhds (1 / 2)) ∧
    (∀ n : ℕ, InSeq n → ∃ m : ℕ, InSeq m ∧ n < m ∧ m ≤ n + 7) := by
  sorry

end OMA.S_oeis_a097324
