import Mathlib

/-!
# A092434: Number of words X=x(1)x(2)x(3)...x(n) of length n in three digits {0,1,2} that are invariant under the mapping X -> Y, where y(i)=((AD)^(i-1))x(1) and where (AD) denotes the absolute difference (AD)x(i)=abs(x(i+1)-x(i)) (in other words, y(i) is the i-th element in the diagonal of leading entries in the table of absolute differences of {x(1), x(2),...,x(n)}).

Source: https://oeis.org/A092434
Credit: @Solfanbtc

Conjecture (OEIS A092434): a(n) = (n+2) * 2^((n-1) div 2) for n >= 1 (offset 1).

Definitions: a word is a function `Fin n → Fin 3`, read as a list x(1), ..., x(n). AD maps a list
to the list of absolute differences of consecutive entries. The word is invariant when, for every
i (0-based, i < n), the first entry of AD^i(X) equals x(i+1). Example from the entry: 2110.
Checked numerically by brute force for n <= 12: the counts are 3, 4, 10, 12, 28, 32, 72, 80, 176,
192, 416, 448, matching both the listed terms and the formula.
-/

namespace OMA.S_oeis_a092434

/-- Absolute differences of consecutive entries. -/
def AD (l : List ℕ) : List ℕ := List.zipWith (fun a b => Nat.dist a b) l l.tail

/-- The word is invariant under X ↦ Y. -/
def IsInvariant {n : ℕ} (w : Fin n → Fin 3) : Prop :=
  let l := List.ofFn fun i => (w i : ℕ)
  ∀ i : ℕ, i < n → (AD^[i] l).headD 0 = l.getD i 0

instance {n : ℕ} (w : Fin n → Fin 3) : Decidable (IsInvariant w) := by
  unfold IsInvariant; infer_instance

/-- a(n): the number of invariant words of length n. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun w : Fin n → Fin 3 => IsInvariant w).card

theorem main : ∀ n : ℕ, 1 ≤ n → a n = (n + 2) * 2 ^ ((n - 1) / 2) := by
  sorry

end OMA.S_oeis_a092434
