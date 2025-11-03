import Mathlib.Tactic.PNatToNat
import Mathlib.Tactic.Ring.PNat
import Mathlib.Tactic.Ring.RingNF

/-!
# Positive Natural Number Exponentiation for Semigroups

This file defines and instantiates an exponentiation operation on semigroups. Exponentiation is
typically defined for natural number exponents, but here we require non-zero natural numbers (`ℕ+`)
because `x^0` is not well-defined in a semigroup context.

This file also contains lemmas about the properties of this exponentiation operation and of the
`ℕ+` type.

## Main definitions

* `Semigroup.pNatPow` - Definition of exponentiation in semigroups using positive naturals.

## Main theorems

In the following statements, `x y : S` and `m n : ℕ+` where `S` is a semigroup:
* `Semigroup.pow_add` - `x ^ m * x ^ n = x ^ (m + n)`.
* `Semigroup.mul_pow_mul` - `(x * y) ^ n * x = x * (y * x) ^ n`.
* `Semigroup.pow_mul_comm` - `x ^ m * x ^ n = x ^ n * x ^ m`.
* `Semigroup.pow_mul_comm'` - `x ^ n * x = x * x ^ n`.
* `Semigroup.pow_mul` - `(x ^ n) ^ m = x ^ (m * n)`.
* `Semigroup.pow_right_comm` - `(x ^ m) ^ n = (x ^ n) ^ m`.
* `Monoid.pow_pNat_to_nat` - `x ^ n = x ^ (n : ℕ)`.
* `WithOne.pow_eq` - `(↑x : WithOne S) ^ n = ↑(x ^ n)`.

## Implementation notes

The `simp`-tagged lemmas collectively normalize power expressions when calling `simp`.
For example, `(a * b) ^ n * (a * b) ^ m * a ^ 1` normalizes to `a * (b * a) ^ (n + m)`.

## References

Analogous definitions and lemmas for exponentiation in monoids can be found in
`Mathlib.Algebra.Group.Defs`.

## Blueprint

This file does not have any blueprint entries.
-/

namespace PNat

variable {m n : ℕ+}

/-- If `m < n` for positive naturals, then there exists a positive `k` such that `n = k + m`. -/
lemma exists_eq_add_of_lt (m_lt_n : m < n) : ∃ (k : ℕ+), n = k + m := by
  use n - m
  pnat_to_nat; omega

/-- For positive naturals, if `m < n` then `m + (n - m) = n`. -/
@[simp] lemma add_sub_cancel' (m_lt_n : m < n) : m + (n - m) = n := by
  induction m using PNat.recOn <;> (pnat_to_nat; omega)

/-- For positive naturals, `n < 2 * n * m`. -/
lemma n_lt_2nm (n m : ℕ+) : n < 2 * n * m := by
  induction m using PNat.recOn with
  | one => pnat_to_nat; omega
  | succ m ih => pnat_to_nat; ring_nf; omega

end PNat

namespace Semigroup

variable {S} [Semigroup S]

/-- Exponentiation for semigroups over positive naturals. -/
def pNatPow (x : S) (n : ℕ+) : S := @PNat.recOn n (fun _ => S) x (fun _ ih => ih * x)

/-- Provides the notation `a ^ n` for `pNatPow a n`. -/
instance hPow : Pow S ℕ+ := ⟨pNatPow⟩

variable (x y : S) (n m : ℕ+)

/-- For any element of a semigroup, raising it to the power `1` gives back the element itself. -/
@[simp] lemma pow_one : x ^ (1 : ℕ+) = x := by rfl

/-- Exponentiation satisfies the successor property. -/
@[simp] lemma pow_succ : (x ^ n) * x = x ^ (n + 1) := by induction n using PNat.recOn <;> rfl

/-- Multiplying powers with the same base is equivalent to exponentiating by the sum. -/
@[simp] lemma pow_add : x ^ m * x ^ n = x ^ (m + n) := by
  induction n using PNat.recOn with
  | one => rw [pow_one, pow_succ]
  | succ k ih => simp_rw [← add_assoc, ← pow_succ, ← mul_assoc, ih]

/-- Multiplicative associativity for powers. -/
@[simp] lemma mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n := by
  induction n using PNat.recOn with
  | one => simp [← mul_assoc]
  | succ n ih => simp only [← pow_succ, ← mul_assoc, ih]

/-- Powers of the same element commute with each other. -/
lemma pow_mul_comm : x ^ m * x ^ n = x ^ n * x ^ m := by rw [pow_add, add_comm, pow_add]

/-- Every power of an element commutes with the element itself. -/
@[simp] lemma pow_mul_comm' : x ^ n * x = x * x ^ n := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rw [← pow_succ, ← mul_assoc, ih]

/-- Taking the power of a power is equivalent to exponentiating by the product. -/
@[simp] lemma pow_mul : (x ^ n) ^ m = x ^ (m * n) := by
  induction m using PNat.recOn with
  | one    => rw [one_mul, pow_one]
  | succ k ih => simp_rw [← pow_succ, ih, pow_add]; congr; ring

/-- Right-associated powers can be rearranged due to commutativity of exponent multiplication. -/
lemma pow_right_comm : (x ^ m) ^ n = (x ^ n) ^ m := by simp only [pow_mul, mul_comm]

end Semigroup

/-- Bridge between positive natural powers and standard natural number powers in monoids. -/
lemma Monoid.pow_pNat_to_nat {M} [Monoid M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => simp
  | succ n' ih =>
    rw [PNat.add_coe]; simp
    rw [← Semigroup.pow_succ, ← Nat.succ_eq_add_one, pow_succ, ih]

/-- Taking powers in the adjunction `S¹` corresponds to taking powers in the semigroup `S`
and then embedding the result. -/
lemma WithOne.pow_eq {S} [Semigroup S] (x : S) (n : ℕ+) : (↑x : WithOne S) ^ n = ↑(x ^ n) := by
  induction n with
  | one => rfl
  | succ n ih => simp_rw [← Semigroup.pow_succ, Semigroup.pow_mul_comm', WithOne.coe_mul, ih]
