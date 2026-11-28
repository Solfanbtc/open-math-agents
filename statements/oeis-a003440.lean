import Mathlib

/-!
# A003440: Number of binary vectors with restricted repetitions.

Source: https://oeis.org/A003440
Credit: @Solfanbtc

The entry carries two conjectures:
1. (Ralf Stephan, 2004) G.f.: `((1-x)^2 * sqrt((1+x+x^2)/(1-3x+x^2)) + x^2 - 1) / (2x^2)`.
2. (R. J. Mathar, 2013) `(n+2)a(n) - 3(n+1)a(n-1) + (n-2)a(n-2) - (n-1)a(n-3)
   + 3(n-4)a(n-4) - (n-5)a(n-5) = 0`.
We state both (their conjunction).

Conventions.
* Definition of a(n). Following K. A. Post's report "Binary Sequences with Restricted
  Repetitions" as read in the entry (J.-P. Levrel's comment and J.-F. Alcover's program
  a(n) = a(n, n)): a(n) is the number of binary words with n zeros and n ones, in which no
  symbol is repeated more than twice in a row (no run of length ≥ 3), and which begin with a
  zero (a(0) = 1: the empty word). A brute-force count gives 1,1,3,7,17,42,104,259,648,1627,
  matching the data; Hanna's formula `Σ_k (C(k,n-k)+C(k+1,n-k-1))^2/2` matches all 30 listed
  terms.
* Conjecture 1. With `A = Σ a(n) x^n` and `F = 2x^2 A + 1 - x^2`, the claim is
  `F = (1-x)^2 S` where `S` is the power series square root of `(1+x+x^2)/(1-3x+x^2)` with
  constant term 1. Since `F` has constant term 1, this is equivalent (in the integral domain
  `ℚ⟦x⟧`) to the polynomial identity `F^2 (1-3x+x^2) = (1-x)^4 (1+x+x^2)`, which is stated.
  (Checked on the listed terms, up to x^29.)
* Conjecture 2 is stated for n ≥ 5, the range where all indices are ≥ 0 (with a(-k) = 0 it
  would fail at n = 0..3, e.g. n = 0 gives 2·a(0) = 2 ≠ 0). Checked for 5 ≤ n ≤ 29 on the data.
-/

namespace OMA.S_oeis_a003440

/-- Binary words of length `2n` with `n` zeros (`false`), starting with a zero, and with no
three consecutive equal letters. -/
def Valid (n : ℕ) (s : Fin (2 * n) → Bool) : Prop :=
  (Finset.univ.filter (fun i => s i = false)).card = n ∧
  (∀ h : 0 < 2 * n, s ⟨0, h⟩ = false) ∧
  ∀ i j k : Fin (2 * n), j.val = i.val + 1 → k.val = i.val + 2 → ¬ (s i = s j ∧ s j = s k)

/-- A003440. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {s : Fin (2 * n) → Bool // Valid n s}

theorem main :
    (let X : PowerSeries ℚ := PowerSeries.X
     let F : PowerSeries ℚ := 2 * X ^ 2 * PowerSeries.mk (fun n => (a n : ℚ)) + 1 - X ^ 2
     F ^ 2 * (1 - 3 * X + X ^ 2) = (1 - X) ^ 4 * (1 + X + X ^ 2)) ∧
    (∀ n : ℕ, 5 ≤ n →
      ((n : ℤ) + 2) * a n - 3 * ((n : ℤ) + 1) * a (n - 1) + ((n : ℤ) - 2) * a (n - 2)
        - ((n : ℤ) - 1) * a (n - 3) + 3 * ((n : ℤ) - 4) * a (n - 4)
        - ((n : ℤ) - 5) * a (n - 5) = 0) := by
  sorry

end OMA.S_oeis_a003440
