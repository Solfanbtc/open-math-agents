import Mathlib

/-!
# A002618: a(n) = n*phi(n).

Source: https://oeis.org/A002618
Credit: @Solfanbtc

Conjecture (Zhi-Wei Sun, from the OEIS entry): all the rational numbers
$\sum_{i=j}^k 1/a(i)$ with $0 < \min\{2,k\} \le j \le k$ have pairwise distinct
fractional parts.

Here $a(n) = n \varphi(n)$ (offset 1). Over natural numbers, $0 < \min\{2,k\}$ means
$1 \le k$, so the admissible index pairs are $(1,1)$ and all $(j,k)$ with $2 \le j \le k$;
in particular $j \ge 1$, so the value $a(0) = 0$ of the Lean formula never occurs.
"Pairwise distinct" is read as: distinct pairs $(j,k)$ give distinct fractional parts.
Checked with exact rational arithmetic for all admissible pairs with $k \le 80$.
-/

namespace OMA.S_oeis_a002618

/-- $a(n) = n \varphi(n)$. -/
def a (n : ℕ) : ℕ := n * n.totient

/-- $\sum_{i=j}^k 1/a(i)$ as a rational number. -/
def recipSum (j k : ℕ) : ℚ := ∑ i ∈ Finset.Icc j k, (1 : ℚ) / (a i : ℚ)

/-- The index condition $0 < \min\{2,k\} \le j \le k$. -/
def IndexCond (j k : ℕ) : Prop := 0 < min 2 k ∧ min 2 k ≤ j ∧ j ≤ k

theorem main : ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄, IndexCond j₁ k₁ → IndexCond j₂ k₂ →
    (j₁, k₁) ≠ (j₂, k₂) → Int.fract (recipSum j₁ k₁) ≠ Int.fract (recipSum j₂ k₂) := by
  sorry

end OMA.S_oeis_a002618
