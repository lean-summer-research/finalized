import Mathlib
import MyProject.Green.Basic

/-!
# Ideals

## Main Definitions

## Main Theorems

## Notation
For `p, q : Ideal' α`, `p ∩ q : Ideal α` denotes their intersection.

`⊤, ∅ : Ideal' α` refer to the full and empty ideals, respectively.

Given `[MulZeroClass α]`, `⊥` represents the ideal `{0}`

## Implementation Notes

The `SetLike` implementation is from the template in the docstring of `Mathlib.Data.Setlike.Basic`.

For an `p : Ideal' α` and `x : α`, the notation `x ∈ (p : Set S)` is perfered over `x ∈ p.carrier`
and this is supported by tagging the `mem_carrier` lemmas with `@[simp]`.

## TODO
is `⊤` the correct notation for the full ideal?
Is it reasonable to define these over all types, not just semigroups?
Should simple semigroups be a typeclass?
Why did the instance not work for bot?
Should we make a new file for regular and simple semigroups?
-/

structure LeftIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mul_mem_mem {x: α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace LeftIdeal

variable {α : Type*} [Mul α] {x y : α}

/-- Allows for notation `∅ : LeftIdeal α`. -/
instance : EmptyCollection (LeftIdeal α) where
  emptyCollection := {
      carrier := ∅
      mul_mem_mem := by simp}

/-- Allows for notation `⊤ : LeftIdeal α` for the full ideal. -/
instance : Top (LeftIdeal α) where
  top := {
      carrier := Set.univ
      mul_mem_mem := by simp}

/-- `SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances. -/
instance : SetLike (LeftIdeal α) α :=
  ⟨LeftIdeal.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : LeftIdeal α} {x : α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : LeftIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : LeftIdeal α} (hin : x ∈ p) : y * x ∈ p := by
  have h := p.mul_mem_mem hin y; simp_all

variable {S : Type*} [Semigroup S]

end LeftIdeal

structure RightIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x: α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier

namespace RightIdeal

variable {α : Type*} [Mul α] {x y : α}

instance : EmptyCollection (RightIdeal α) where
  emptyCollection := {
      carrier := ∅
      mem_mul_mem := by simp}

instance : Top (RightIdeal α) where
  top := {carrier := Set.univ,
          mem_mul_mem := by simp_all}

/-- `SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances. -/
instance : SetLike (RightIdeal α) α :=
  ⟨RightIdeal.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : RightIdeal α} {x : α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : RightIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : RightIdeal α} (hin : x ∈ p) : x * y ∈ p := by
  have h := p.mem_mul_mem hin y; simp_all

variable {S : Type*} [Semigroup S]

end RightIdeal

structure Ideal' (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x: α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier
  mul_mem_mem {x: α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace Ideal'

variable {α : Type*} [Mul α] {x y z : α}

/-- `SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances. -/
instance : SetLike (Ideal' α) α :=
  ⟨Ideal'.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

/-- The intersection of two ideals is an ideal. -/
instance : Inter (Ideal' α) where
  inter p q := {
    carrier := (p : Set α) ∩ (q : Set α)
    mem_mul_mem := by
      intros x hx y
      rcases hx with ⟨hxp, hxq⟩
      constructor
      · exact p.mem_mul_mem hxp y -- Proof for `x * y ∈ p.carrier`
      · exact q.mem_mul_mem hxq y -- Proof for `x * y ∈ q.carrier`
    mul_mem_mem := by
      intros x hx y
      rcases hx with ⟨hxp, hxq⟩
      constructor
      · exact p.mul_mem_mem hxp y -- Proof for `y * x ∈ p.carrier`
      · exact q.mul_mem_mem hxq y -- Proof for `y * x ∈ q.carrier`
  }

@[simp] lemma inter_coe {p q : Ideal' α} : (p ∩ q).carrier = (p : Set α) ∩ (q : Set α) := rfl

instance : EmptyCollection (Ideal' α) where
  emptyCollection := {
      carrier := ∅
      mem_mul_mem := by simp
      mul_mem_mem := by simp}

instance : Top (Ideal' α) where
  top := {carrier := Set.univ,
          mem_mul_mem := by simp_all,
          mul_mem_mem := by simp_all}

/- Why does this not work?
I think it is seeing the wrong Mul instance
instance [MulZeroClass α] : Bot (Ideal' α) where
  bot := {carrier := {0}
          mem_mul_mem := by
            intros x h y
            simp_all
            have h := zero_mul y
            nth_rw 2 [← h]
            sorry
            -- rfl does not work
          mul_mem_mem := by sorry}
-/

instance {β : Type*} [MulZeroClass β] : Bot (Ideal' β) where
  bot := {carrier := {0}
          mem_mul_mem := by simp
          mul_mem_mem := by simp
  }

def toLeftIdeal (p : Ideal' α) : LeftIdeal α where
  carrier := p.carrier
  mul_mem_mem := p.mul_mem_mem


def toRightIdeal (p : Ideal' α) : RightIdeal α where
  carrier := p.carrier
  mem_mul_mem := p.mem_mul_mem


@[simp] lemma mem_carrier {p : Ideal' α} {x : α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

@[simp] lemma coe_top : ((⊤ : Ideal' α) : Set α) = Set.univ := rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : Ideal' α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : Ideal' α} (hin : x ∈ p) : z * x * y ∈ p := by
  have h := p.mul_mem_mem hin z
  simp_all
  have h₂ := p.mem_mul_mem h y
  simp_all

@[simp] lemma mul_right_mem {p : Ideal' α} (hin : x ∈ p) : x * y ∈ p := by
  have h := p.mem_mul_mem hin y
  simp_all

@[simp] lemma mul_left_mem {p : Ideal' α} (hin : x ∈ p) : y * x ∈ p := by
  have h := p.mul_mem_mem hin y
  simp_all

end Ideal'

/-
### Regular Semigroups
-/

section Regular


def isRegularElem {α : Type*} [Mul α] (x : α) : Prop :=
  ∃ y : α, x * y * x = x

variable {S : Type*}

class RegularSemigroup (S : Type*) extends Semigroup S where
  isRegular : ∀ x : S, isRegularElem x

@[simp] lemma RegularSemigroup.regular [inst : RegularSemigroup S] (x : S) :
    ∃ y : S, x * y * x = x := inst.isRegular x

end Regular

/-
### Simple Semigroups
-/

/-- A semigroup is simple if its only ideals are `⊥` and `∅` -/
class SimpleSemigroup (S : Type*) extends Semigroup S where
  ideal_eq : ∀ (I : Ideal' S), I = ∅ ∨ I = ⊤

@[simp] lemma SimpleSemigroup.ideal [inst : SimpleSemigroup S] (I : Ideal' S) :
    I = ∅ ∨ I = ⊤ := inst.ideal_eq I

class ZeroSimpleSemigroup (S : Type*) extends SemigroupWithZero S where
  ideal_eq : ∀ (I : Ideal' S), I = ∅ ∨ I = ⊤ ∨ I = ⊥

@[simp] lemma ZeroSimpleSemigroup.ideal [inst : ZeroSimpleSemigroup S] (I : Ideal' S) :
    I = ∅ ∨ I = ⊤ ∨ I = ⊥ := inst.ideal_eq I

namespace Semigroup

/-- In a simple semigroup, all elements are J-preorder related -/
lemma JPreorder.ofSimple [SimpleSemigroup S] (x y : S) : x ≤𝓙 y := by
  sorry

instance JPreorder.toSimpleSemigroup [Semigroup S] (h : ∀ x y : S, x ≤𝓙 y) : SimpleSemigroup S := by
  sorry

lemma JPreorder.ofZeroSimple [ZeroSimpleSemigroup S] (x y : S) (hne : y ≠ 0) :
    x ≤𝓙 y := by
  sorry

instance JPreorder.toZeroSimpleSemigroup [SemigroupWithZero S] (h : ∀ x y : S, x ≤𝓙 y) :
    ZeroSimpleSemigroup S := by
  sorry

end Semigroup
