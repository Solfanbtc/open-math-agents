import Mathlib

/-!
# A023634: s(3n)-s(3n-1), where s( ) is sequence A023633.

Source: https://oeis.org/A023634
Credit: @Solfanbtc

Conjecture (Michel Dekking, Sep 15 2022, in the entry): (a(n)) is the fixed point of the
morphism 2 -> 5, 4 -> 422, 5 -> 5222 (and so, since a(n) = b(n) + 1 with b the first differences
of the complement of A023633, (b(n)) is the fixed point of 1 -> 4, 3 -> 311, 4 -> 4111; this
second form is a direct consequence, so only the first is stated).

Conventions.
* A023633 (offset 1) is defined in its entry by s(1) = 1, s(2) = 2, s(n) = c(floor(n/3)) + n,
  where c = complement of s; as in Dekking's comment, c is indexed from 0 and is the increasing
  enumeration of the naturals (including 0) not of the form s(j), j ≥ 1: c = 0, 3, 4, 5, 9, ...
  `IsA023633 s` is this defining property, with `Nat.nth` the 0-indexed enumeration (s 0 is
  unused). The statement asserts that such an s exists and that every such s satisfies the
  conjecture (python3 computes it: 1, 2, 6, 7, 8, 10, 11, 12, 14, ..., matching A023633).
* a(n) = s(3n) - s(3n-1) for n ≥ 1 (offset 1: 4, 2, 2, 5, 5, 5, 2, ...).
* The fixed point starts with 4 (a(1) = 4, and 4 -> 422 starts with 4). "a is the fixed point"
  is stated as: for every k, the word mu^k(4) is a prefix of a(1), a(2), ...; these words have
  unbounded length. Checked: mu^9(4) (1789 letters) agrees with a.
-/

namespace OMA.S_oeis_a023634

/-- The defining property of A023633: s(1) = 1, s(2) = 2, s(n) = c(floor(n/3)) + n for n ≥ 3,
where c is the complement of {s(j) : j ≥ 1} in ℕ, enumerated from index 0. -/
def IsA023633 (s : ℕ → ℕ) : Prop :=
  s 1 = 1 ∧ s 2 = 2 ∧
    ∀ n : ℕ, 3 ≤ n → s n = Nat.nth (fun m => ∀ j : ℕ, 1 ≤ j → s j ≠ m) (n / 3) + n

/-- The morphism 2 -> 5, 4 -> 422, 5 -> 5222. -/
def mu : ℕ → List ℕ
  | 2 => [5]
  | 4 => [4, 2, 2]
  | 5 => [5, 2, 2, 2]
  | _ => []

/-- `mu^k` applied to the word `4`. -/
def W : ℕ → List ℕ
  | 0 => [4]
  | k + 1 => (W k).flatMap mu

theorem main :
    (∃ s : ℕ → ℕ, IsA023633 s) ∧
    ∀ s : ℕ → ℕ, IsA023633 s →
      ∀ (k i : ℕ) (h : i < (W k).length), s (3 * (i + 1)) - s (3 * (i + 1) - 1) = (W k)[i] := by
  sorry

end OMA.S_oeis_a023634
