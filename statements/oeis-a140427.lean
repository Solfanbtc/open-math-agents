import Mathlib

/-!
# A140427: Arises in relating doubly-even error-correcting codes, graphs and irreducible representations of N-extended supersymmetry.

Source: https://oeis.org/A140427 (Jonathan Vos Post, 2008; conjecture by Sean A. Irvine,
Jul 19 2022; OEIS Foundation, CC BY-SA 4.0). Reference: C. F. Doran, M. G. Faux, S. J. Gates Jr,
T. Hubsch, K. M. Iga and G. D. Landweber, arXiv:0806.0051, formula (13).
Credit: @Solfanbtc

Definition (OEIS formula): a(n) = 0 for 0 <= n < 4, a(n) = floor((n-4)^2/4) + 1 for
n = 4, 5, 6, 7, and a(n) = a(n-8) + 4 for n > 7.

Conjecture (OEIS): A140427 is "essentially partial sums of A169675" (verified for n <= 10000).
A169675 is the lexicographically earliest de Bruijn sequence for n = 3 and k = 2, i.e. the
lexicographically least binary cyclic word of length 2^3 = 8 containing every binary word of
length 3 exactly once as a cyclic factor, repeated periodically (offset 0).

Formalization notes.
* "Essentially" is made precise by the data: a(n) = A169675(0) + ... + A169675(n-1) for all
  n ≥ 0 (the partial sums shifted by one index; a(0) = 0 is the empty sum). Lean #eval confirms
  this against the 63 listed terms (and that 0,0,0,1,0,1,1,1 is the least of the 16 binary de
  Bruijn words), and the shift is the only one that fits (the unshifted
  partial sums start 0, 0, 0, 1, while A140427 starts 0, 0, 0, 0, 1).
* A169675 is not hard-coded: the statement quantifies over the lexicographically least de
  Bruijn word `w` (lexicographic order on `List ℕ`); A169675(i) = w[i mod 8]. Such a word
  exists (0, 0, 0, 1, 0, 1, 1, 1 is one, and there are finitely many binary words of length 8),
  so the statement is not vacuous.
-/

namespace OMA.S_oeis_a140427

/-- A140427, by its defining formula. -/
def a : ℕ → ℕ
  | n + 8 => a n + 4
  | n => if n < 4 then 0 else (n - 4) ^ 2 / 4 + 1

/-- `w` is a binary de Bruijn word for words of length 3: it has length 8 and every binary
word `u` of length 3 occurs exactly once as a cyclic factor. -/
def IsDeBruijn (w : List ℕ) : Prop :=
  w.length = 8 ∧ (∀ x ∈ w, x < 2) ∧
  ∀ u : Fin 3 → Fin 2, ∃! i : Fin 8, ∀ j : Fin 3, w.getD ((i.val + j.val) % 8) 0 = (u j).val

theorem main : ∀ w : List ℕ, IsDeBruijn w → (∀ w' : List ℕ, IsDeBruijn w' → w ≤ w') →
    ∀ n : ℕ, a n = ∑ i ∈ Finset.range n, w.getD (i % 8) 0 := by
  sorry

end OMA.S_oeis_a140427
