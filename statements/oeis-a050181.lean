import Mathlib

/-!
# A050181: T(2n+3, n), array T as in A051168; a count of Lyndon words.

Source: https://oeis.org/A050181
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jul 20 2016, OEIS A050181): for n >= 5 (offset 0, so that a(n-5) is a
term),
  -(n-1)(n+3)(n+2) a(n) + 2(3n-4)(n+2)(n+1) a(n-1) - 4n(n+1)(2n-5) a(n-2)
  + 2(n-1)(n+2)(2n-3) a(n-3) - 4(2n-5)(3n-4)(n+1) a(n-4) + 8n(2n-5)(2n-7) a(n-5) = 0.
Status: the entry says (Petros Hadjicostas, Nov 16 2017) that the conjecture can be verified from
the closed form a(n) = (1/(2n+3)) Σ_{d | gcd(n,3)} mu(d) binomial((2n+3)/d, n/d); stated faithfully.

Definition. T(h, k) (A051168) is the number of binary Lyndon words with k ones and h - k zeros: a
word w of length h is Lyndon when it is strictly smaller, in lexicographic order with 0 < 1, than
each of its nontrivial rotations (`lexLt`, lexicographic, written out). Words are functions
`Fin h → Fin 2`, read as lists of naturals.
a(n) = T(2n+3, n). Checked numerically: brute force gives 0, 1, 3, 9, 30, 99 for n <= 5, the closed
form gives all listed terms, and the recurrence holds for 5 <= n < 200.
-/

namespace OMA.S_oeis_a050181

/-- The word as a list of digits. -/
def toList {h : ℕ} (w : Fin h → Fin 2) : List ℕ := List.ofFn fun i => (w i : ℕ)

/-- Strict lexicographic order on lists of naturals (a proper prefix is smaller). -/
def lexLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: l, y :: m => x < y || (x == y && lexLt l m)

/-- `w` is a Lyndon word: smaller than all its nontrivial rotations. -/
def IsLyndon {h : ℕ} (w : Fin h → Fin 2) : Prop :=
  ∀ r : Fin h, 0 < (r : ℕ) → lexLt (toList w) ((toList w).rotate r) = true

instance {h : ℕ} (w : Fin h → Fin 2) : Decidable (IsLyndon w) := by
  unfold IsLyndon; infer_instance

/-- T(h, k): binary Lyndon words of length `h` with `k` ones. -/
def T (h k : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin h → Fin 2 => (toList w).count 1 = k ∧ IsLyndon w).card

/-- a(n) = T(2n + 3, n). -/
def a (n : ℕ) : ℕ := T (2 * n + 3) n

theorem main : ∀ n : ℕ, 5 ≤ n →
    -((n : ℤ) - 1) * (n + 3) * (n + 2) * a n + 2 * (3 * (n : ℤ) - 4) * (n + 2) * (n + 1) * a (n - 1)
      - 4 * (n : ℤ) * (n + 1) * (2 * n - 5) * a (n - 2)
      + 2 * ((n : ℤ) - 1) * (n + 2) * (2 * n - 3) * a (n - 3)
      - 4 * (2 * (n : ℤ) - 5) * (3 * n - 4) * (n + 1) * a (n - 4)
      + 8 * (n : ℤ) * (2 * n - 5) * (2 * n - 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a050181
