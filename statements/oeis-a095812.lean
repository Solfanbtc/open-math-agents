import Mathlib

/-!
# A095812: Greatest number, not divisible by 4, having exactly n partitions into three positive squares

Source: https://oeis.org/A095812
The entry lists, for `n = 1, ..., 34`, the greatest number `m` with `4 ∤ m` that has exactly `n`
partitions into three positive squares (`m = x^2 + y^2 + z^2` with `1 ≤ x ≤ y ≤ z`, unordered).
The entry says: "These are conjectured values" (the program checks numbers up to 10^6; the
b-file is checked up to 10^8).

We state the conjecture for all 34 listed terms: for each `n` in `1..34`, `a(n)` is not divisible
by 4, has exactly `n` such partitions, and every `m` with `4 ∤ m` and exactly `n` such partitions
satisfies `m ≤ a(n)` (so the greatest such number exists and equals `a(n)`).

Checked with python3: for all `m < 10^6`, the greatest `m` with `4 ∤ m` and exactly `n`
partitions is the listed `a(n)`, for each `n ≤ 34`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a095812

/-- The number of partitions of `m` into three positive squares:
triples `1 ≤ x ≤ y ≤ z` with `x^2 + y^2 + z^2 = m`. -/
def r3 (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = m)).card

/-- The listed terms `a(1), ..., a(34)` (index `0` of the list is `a(1)`). -/
def terms : List ℕ :=
  [793, 1885, 3763, 6307, 13843, 16003, 21547, 34483, 48427, 54763, 85507, 90787,
    111763, 103387, 166147, 137083, 222643, 211843, 289963, 253507, 296587,
    319867, 462883, 375523, 393187, 546067, 502483, 532123, 615883, 590947, 662803, 991027,
    703123, 958483]

theorem main : ∀ i : ℕ, (hi : i < terms.length) →
    ¬ 4 ∣ terms[i] ∧ r3 terms[i] = i + 1 ∧
      ∀ m : ℕ, ¬ 4 ∣ m → r3 m = i + 1 → m ≤ terms[i] := by
  sorry

end OMA.S_oeis_a095812
