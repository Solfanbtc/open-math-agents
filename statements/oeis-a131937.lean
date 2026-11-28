import Mathlib

/-!
# A131937: a(1)=1; a(2)=4, a(n) = a(n-1) + (n-th positive integer which does not occur in sequence A131938).

Source: https://oeis.org/A131937 (Leroy Quet, 2007; conjecture by Gregory Gerard Wojnar,
Dec 12 2024; OEIS Foundation, CC BY-SA 4.0). Companion: A131938 (a(1) = 2; a(2) = 5,
a(n) = a(n-1) + (n-th positive integer which does not occur in A131937)).
Credit: @Solfanbtc

Conjecture (OEIS): Starting with any infinite positive integer sequence A1(n) whose complement
is also infinite, let B1(n) be the sequence of partial sums of the complement of sequence A1.
Let A2(n) be the sequence of partial sums of the complement of sequence B1. Iteratively let
B[k](n) be the sequence of partial sums of the complement of sequence A[k], and let A[k+1](n)
be the sequence of partial sums of the complement of sequence B[k]. Call the stable iterative
limit sequences A(n) and B(n), which are universal and do not depend upon the initial sequence
A1(n). These two limiting sequences are conjectured to be A131938 and this A131937.

Formalization notes.
* Sequences of positive integers are handled through their sets of values; the complement of
  a set S is {x > 0 | x ∉ S}, listed increasingly with `Nat.nth`, and the n-th partial sum
  (n ≥ 1) of the complement is the sum of its first n elements.
* "Stable iterative limit" is read as: for every index n ≥ 1, the n-th terms A[k](n) and
  B[k](n) are eventually constant in k, equal to A(n) and B(n).
* Which limit is which depends on the start: if 1 ∈ A1, then 1 ∈ A[k] for every k, so A[k] can
  only converge to A131937 (whose first term is 1); if 1 ∉ A1, then 1 ∈ B1 and A[k] converges to
  A131938. (Python: from the even numbers, the primes or a random set, (A, B) stabilizes to
  (A131938, A131937); from the odd numbers, the squares or a set containing 1, ..., 100, to
  (A131937, A131938), in all cases on the first 52 terms within 4 rounds.) The literal claim
  that the ordered pair is universal therefore fails at a trivial value. The minimal fix,
  stated here, is that the limits exist and form the pair {A131938, A131937} in one of the two
  orders. The source names the two sequences without assigning an order.
* A131937 and A131938 are given by their mutual definitions (`IsQuetPair`), with OEIS indices
  n ≥ 1 (index 0 is unused), and the claim is stated for every pair meeting the definitions.
  Python confirms that the 52 listed terms of each are the partial sums of the complement of
  the other.
-/

namespace OMA.S_oeis_a131937

/-- The complement {x > 0 | x ∉ S} of a set of positive integers. -/
def compl (S : Set ℕ) : Set ℕ := {x | 0 < x ∧ x ∉ S}

/-- The n-th partial sum (n ≥ 1) of the increasing listing of the complement of `S`. -/
noncomputable def psumCompl (S : Set ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, Nat.nth (· ∈ compl S) i

/-- The set of values of the partial sums of the complement of `S`. -/
def T (S : Set ℕ) : Set ℕ := {y | ∃ n, 1 ≤ n ∧ y = psumCompl S n}

/-- `Aset S k` is (the set of values of) A[k+1], starting from A1 = S. -/
def Aset (S : Set ℕ) : ℕ → Set ℕ
  | 0 => S
  | k + 1 => T (T (Aset S k))

/-- n-th term (n ≥ 1) of B[k+1] = partial sums of the complement of A[k+1]. -/
noncomputable def Bseq (S : Set ℕ) (k n : ℕ) : ℕ := psumCompl (Aset S k) n

/-- n-th term (n ≥ 1) of A[k+2] = partial sums of the complement of B[k+1]. -/
noncomputable def Aseq (S : Set ℕ) (k n : ℕ) : ℕ := psumCompl (T (Aset S k)) n

/-- n-th positive integer (n ≥ 1) not among the values f(1), f(2), .... -/
noncomputable def nonMember (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun x => 0 < x ∧ ∀ i, 1 ≤ i → f i ≠ x) (n - 1)

/-- `a` is A131937 and `b` is A131938, by their definitions in the OEIS. -/
def IsQuetPair (a b : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 4 ∧ (∀ n, 3 ≤ n → a n = a (n - 1) + nonMember b n) ∧
  b 1 = 2 ∧ b 2 = 5 ∧ (∀ n, 3 ≤ n → b n = b (n - 1) + nonMember a n)

theorem main : ∀ a b : ℕ → ℕ, IsQuetPair a b →
    ∀ S : Set ℕ, (∀ x ∈ S, 0 < x) → S.Infinite → (compl S).Infinite →
      (∀ n, 1 ≤ n → ∃ K, ∀ k, K ≤ k → Aseq S k n = b n ∧ Bseq S k n = a n) ∨
      (∀ n, 1 ≤ n → ∃ K, ∀ k, K ≤ k → Aseq S k n = a n ∧ Bseq S k n = b n) := by
  sorry

end OMA.S_oeis_a131937
