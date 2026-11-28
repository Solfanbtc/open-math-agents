import Mathlib

/-!
# A089781: Successive coprime numbers with distinct successive differences: gcd(a(k+1),a(k)) = gcd(a(m+1),a(m)) = 1 and a(k+1)-a(k) = a(m+1)-a(m) <==> m=k.

Source: https://oeis.org/A089781
Credit: @Solfanbtc

The sequence is greedy (formula of R. Zumkeller): `a(1) = 1` and `a(k+1) = a(k) + d`, where `d` is
the smallest positive integer, not already used as a difference, that is coprime to `a(k)`
(equivalently `gcd(a(k+1), a(k)) = 1`). Example: after 1, 2 comes 5 (difference 1 used, 4 not
coprime to 2). `state k = (a(k+1), [differences used so far])`. Checked with python3: this
reproduces the data 1, 2, 5, 7, 11, 16, 23, ...

Conjecture (A. Murthy): there is a constant `C` such that if `a(k+1) - a(k) = n` then `k < C n`.
`main` states: some real `C` satisfies `k < C · (a(k+1) - a(k))` for all `k ≥ 1`. (python3: over
the first 20000 terms, `k / (a(k+1) - a(k))` is at most 1.5.)
-/

namespace OMA.S_oeis_a089781

/-- `state k = (a(k+1), list of the first k differences)`. -/
noncomputable def state : ℕ → ℕ × List ℕ
  | 0 => (1, [])
  | k + 1 =>
    let s := state k
    let d := sInf {d : ℕ | 1 ≤ d ∧ d ∉ s.2 ∧ Nat.Coprime d s.1}
    (s.1 + d, s.2 ++ [d])

/-- `a k` (offset 1). -/
noncomputable def a (k : ℕ) : ℕ := (state (k - 1)).1

theorem main :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → (k : ℝ) < C * ((a (k + 1) : ℝ) - a k) := by
  sorry

end OMA.S_oeis_a089781
