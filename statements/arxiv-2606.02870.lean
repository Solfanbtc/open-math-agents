import Mathlib

/-!
# On maximal Dynkin friezes

Source: https://arxiv.org/abs/2606.02870
Credit: @Solfanbtc

The abstract constructs friezes of types `B_n` and `D_n` over the positive integers with largest
entries `F_{n+1} F_{n+2} - 1` (type `B_n`) and `F_n F_{n+1} - 1` (type `D_n`), `F_k` the `k`-th
Fibonacci number, and conjectures: *these are the maximal possible entries for their respective
Dynkin types*. We state that the set of all entries of all positive integral friezes of the given
type has exactly this greatest element (`IsGreatest`: attained, which the paper proves, and an upper
bound, which is the conjecture).

## Definitions

A frieze of Dynkin type `Δ` over the positive integers is a ring homomorphism from the cluster
algebra (without coefficients) of type `Δ` to `ℤ` sending every cluster variable to a positive
integer; its entries are the values of the cluster variables. Such a frieze is determined by the
values `a i` on an initial cluster, and conversely positive integers `a i` give a frieze iff every
cluster variable, evaluated at `a`, is an integer (it is then automatically positive, the exchange
relations being subtraction-free).

We use a bipartite initial seed: vertices split by a parity `par`, and the bipartite belt
`belt E par a t` alternately mutates all vertices of parity `t % 2`, with the exchange relation
`x_k x_k' = 1 + ∏_j x_j ^ E j k` (`E j k = |b_{jk}|`, `0` for non-neighbours). In finite type every
cluster variable occurs in the bipartite belt `(x_{i;t})_{t ∈ ℤ}`, which is periodic
(Fomin-Zelevinsky, Cluster algebras II, Thm 1.9; Y-systems and generalized associahedra), so
`t ∈ ℕ` already lists all cluster variables.

* Type `B_n` (`n ≥ 2`): chain `0 - 1 - ... - (n-1)`; the double bond is `E (n-1) (n-2) = 2`,
  `E (n-2) (n-1) = 1`. Calibration (python3): this orientation has 6 and 21 positive integral
  friezes for `n = 2, 3`, with maximal entries `5 = F_3 F_4 - 1` and `14 = F_4 F_5 - 1`, while the
  other orientation (type `C_3`) has `20 = binom 6 3` friezes and maximal entry 13; type `C_n`
  friezes are counted by `binom (2n) n` (Fontaine-Plamondon), so this orientation is `B_n`.
  For `n = 1` the formula gives `F_2 F_3 - 1 = 1` while type `A_1` has entry `2`, so `n ≥ 2`
  (`B_n` is a Dynkin type only for `n ≥ 2`).
* Type `D_n` (`n ≥ 4`, the usual range): chain `0 - ... - (n-3)` with the two leaves `n-2` and
  `n-1` attached to `n-3`; all bonds simple. Calibration: `D_4` has 51 friezes (Fontaine-Plamondon
  count) and maximal entry `14 = F_4 F_5 - 1`.

`Nat.fib` has `fib 1 = fib 2 = 1`, the usual `F_k`.
-/

namespace OMA.S_arxiv_2606_02870

/-- One step of the bipartite belt: at step `t`, mutate every vertex of parity `t % 2`. -/
def mutStep (n : ℕ) (E : Fin n → Fin n → ℕ) (par : Fin n → ℕ) (t : ℕ) (x : Fin n → ℚ) :
    Fin n → ℚ :=
  fun k => if par k = t % 2 then (1 + ∏ j, x j ^ E j k) / x k else x k

/-- The bipartite belt starting from the initial values `a`: `belt E par a t i = x_{i;t}`. -/
def belt (n : ℕ) (E : Fin n → Fin n → ℕ) (par : Fin n → ℕ) (a : Fin n → ℕ) : ℕ → Fin n → ℚ
  | 0 => fun i => (a i : ℚ)
  | t + 1 => mutStep n E par t (belt n E par a t)

/-- `a` (values on the initial cluster) defines a frieze over the positive integers: all initial
values are positive and every cluster variable evaluates to an integer. -/
def IsPosIntFrieze (n : ℕ) (E : Fin n → Fin n → ℕ) (par : Fin n → ℕ) (a : Fin n → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ ∀ t i, ∃ m : ℤ, belt n E par a t i = m

/-- All entries of all positive integral friezes of the given type. -/
def entries (n : ℕ) (E : Fin n → Fin n → ℕ) (par : Fin n → ℕ) : Set ℕ :=
  {v | ∃ a, IsPosIntFrieze n E par a ∧ ∃ t i, belt n E par a t i = v}

/-- Exchange exponents for type `B_n`. -/
def bExp (n : ℕ) (j k : Fin n) : ℕ :=
  if j.val + 1 = k.val ∨ k.val + 1 = j.val then
    (if j.val = n - 1 ∧ k.val = n - 2 then 2 else 1)
  else 0

/-- Bipartite parity for the chain. -/
def bPar (n : ℕ) (k : Fin n) : ℕ := k.val % 2

/-- Exchange exponents for type `D_n`. -/
def dExp (n : ℕ) (j k : Fin n) : ℕ :=
  if (j.val + 1 = k.val ∧ k.val ≤ n - 2) ∨ (k.val + 1 = j.val ∧ j.val ≤ n - 2) ∨
      (j.val = n - 3 ∧ k.val = n - 1) ∨ (k.val = n - 3 ∧ j.val = n - 1) then 1
  else 0

/-- Bipartite parity for `D_n`: the leaf `n-1` has the parity of the leaf `n-2`. -/
def dPar (n : ℕ) (k : Fin n) : ℕ := if k.val = n - 1 then (n - 2) % 2 else k.val % 2

theorem main :
    (∀ n ≥ 2, IsGreatest (entries n (bExp n) (bPar n)) (Nat.fib (n + 1) * Nat.fib (n + 2) - 1)) ∧
    (∀ n ≥ 4, IsGreatest (entries n (dExp n) (dPar n)) (Nat.fib n * Nat.fib (n + 1) - 1)) := by
  sorry

end OMA.S_arxiv_2606_02870
