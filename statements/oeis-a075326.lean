import Mathlib

/-!
# A075326: Anti-Fibonacci numbers: start with a(0) = 0, and extend by the rule that the next term is the sum of the two smallest numbers that are not in the sequence nor were used to form an earlier sum.

Source: https://oeis.org/A075326
Credit: @Solfanbtc

Conjectures (Augusto Santi, OEIS A075326, comments, Aug 16 2025):
1. After the first 0, the residues (mod 5) all fall in the classes 3 and 4. More generally, for
   k-nacci sequences the residue classes (mod k^2+1) all fall in k consecutive ones, the first
   being ceiling((k^2+1)/2).
2. The sequence contains the arithmetic progressions 10k+3, 20k+9 and 40k+18 (stated in the
   entry as known, after Zaslavsky's formula). These three progressions cover, experimentally,
   87.5% = 7/8 of the entire sequence. The remaining terms all belong to two forms: 40k+38 and
   40k+39.
3. The sequence contains all the squares of the numbers of the form 10k+3 and 10k+7, and all
   the cubes of the numbers of the form 10k+7, for k >= 0.
`main` is the conjunction of: the general k-nacci form of 1 (its case k = 2 is the mod 5
claim), the two claims of 2 that are not stated as known, and 3.
(Santi's preceding observation on the algorithm applied to the integers minus the multiples of
3, and its recursive iteration, is not listed among the conjectures and is not stated.)

Conventions:
* `anti k n`: start from `anti k 0 = 0`; at each step take the `k` smallest positive integers
  not crossed off yet, cross them off, and the next term is their sum, which is also crossed off.
  For k = 2 this is A075326 (offset 0); for k = 3 it is the anti-tribonacci A265389 (with an
  extra 0 in front), the "anti-k-nacci" sequences of the entry.
* "k-nacci" is read for k ≥ 2: for k = 1 every positive integer occurs and the claim is false,
  so k ≥ 2 is the minimal reading. ceiling((k^2+1)/2) is written `(k^2 + 2) / 2`; "fall in k
  consecutive classes" is: every term after the first 0 is `≡ c + i (mod k^2+1)` for some `i < k`.
* "cover 7/8 of the entire sequence" is read as a natural density along the indices: the
  proportion of `n ∈ [1, N]` with `anti 2 n` in one of the three progressions tends to 7/8.
* Checked in Python: `anti 2` reproduces %S, %T, %U; for k = 2..8 (10^5 terms each) the
  residues are exactly the k claimed classes; for the first 3·10^5 terms the forms of 2 hold,
  the proportion is 0.875 at N = 10^3, 10^4, 10^5, 3·10^5, and the squares and cubes of 3 below
  the largest computed term all occur.
-/

namespace OMA.S_oeis_a075326

open Filter Topology

/-- The least positive integer not in `S`. -/
def leastNew (S : Finset ℕ) : ℕ :=
  Nat.find (⟨S.sup id + 1, Nat.succ_pos _, fun h => by
    have := Finset.le_sup (f := id) h
    exact absurd this (Nat.not_succ_le_self _)⟩ : ∃ m, 0 < m ∧ m ∉ S)

/-- Cross off the `j` least new positive integers; returns the new set and their sum. -/
def pick : ℕ → Finset ℕ → Finset ℕ × ℕ
  | 0, S => (S, 0)
  | j + 1, S =>
    let m := leastNew S
    let r := pick j (insert m S)
    (r.1, m + r.2)

/-- The crossed-off set and the last term after `n` steps of the anti-`k`-nacci procedure. -/
def state (k : ℕ) : ℕ → Finset ℕ × ℕ
  | 0 => (∅, 0)
  | n + 1 =>
    let r := pick k (state k n).1
    (insert r.2 r.1, r.2)

/-- The anti-`k`-nacci sequence; `anti 2` is A075326. -/
def anti (k n : ℕ) : ℕ := (state k n).2

/-- Membership in one of the three known progressions `10k+3`, `20k+9`, `40k+18`. -/
def InAP (x : ℕ) : Prop := x % 10 = 3 ∨ x % 20 = 9 ∨ x % 40 = 18

instance : DecidablePred InAP := fun x => by unfold InAP; infer_instance

/-- Santi's conjectures on the anti-Fibonacci numbers. -/
theorem main :
    (∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, 1 ≤ n →
        ∃ i < k, anti k n % (k ^ 2 + 1) = (k ^ 2 + 2) / 2 + i) ∧
    (∀ n : ℕ, 1 ≤ n → InAP (anti 2 n) ∨ anti 2 n % 40 = 38 ∨ anti 2 n % 40 = 39) ∧
    Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter fun n => InAP (anti 2 n)).card : ℝ) / N) atTop (𝓝 (7 / 8)) ∧
    (∀ j : ℕ, (∃ n, anti 2 n = (10 * j + 3) ^ 2) ∧ (∃ n, anti 2 n = (10 * j + 7) ^ 2) ∧
        ∃ n, anti 2 n = (10 * j + 7) ^ 3) := by
  sorry

end OMA.S_oeis_a075326
