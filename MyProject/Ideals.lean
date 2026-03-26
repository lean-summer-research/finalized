import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Data.SetLike.Basic
import MyProject.Green.Defs

/-!
# Ideals
This file defines Left/Right/Two-sided ideals in magmas as bundled Set-Like structures. We also
provide functions that return the minimum ideal containing a set/element in semigroups.

We also give an ideal-based characterization of Green's Relations in semigroups.

We also define typeclasses for simple, zero-simple, and regular semigroups.

## Main Definitions
- `LeftIdeal` - A Set-Like structure for sets closed under left multiplication.
- `LeftIdeal.inter` - The intersection of two ideals as an ideal.
- `LeftIdeal.ofSet` - The minimum left ideal containing a set.

- `RightIdeal` - A Set-Like structure for sets closed under right multiplication.
- `RightIdeal.inter` - The intersection of two ideals as an ideal.
- `RightIdeal.ofSet` - The minimum right ideal containing a set.

- `Ideal'` - A Set-Like structure for sets closed under multiplication.
- `Ideal'.inter` - The intersection of two ideals as an ideal.
- `Ideal'.ofSet` - The minimum ideal containing a set.

- `SimpleSemigroup` - A class that extends `Semigroup` with a proof that all ideals
are empty or full.
- `ZeroSimpleSemigroup` - A class that entends `SemigroupWithZero` with a proof that
all ideas are empty, full, or the zero ideal.

- `JPreorder.toSimpleSemigroup` - Given that all elements of a semigroup are 𝓙-preorder related,
an instance for `SimpleSemigroup`
- `JPreorder.toZeroSimpleSemigroup` - Given that all non-zero elements of a semigroup with zero
are 𝓙-preorder related, an instance for `ZeroSimpleSemigroup`

- `isRegularElem` is a predicate on elements `x` in a magma stating that there exists a `y` such
that `x * y * x = x`.
- `RegularSemigroup` is a class extending `Semigroup` with a proof that every element is regular.

## Main Theorems
- `LeftIdeal.mem` - Left Ideals are closed under left multiplication.
- `RightIdeal.mem` - Right Ideals are closed under right multiplication.
- `Ideal'.mul_left_mem` - Ideals are closed under left multiplication.
- `Ideal'.mul_right_mem` - Ideals are closed under right multiplication.
- `Ideal'.mem` - Ideals are closed under two-sided multiplication.

Let `x y` be elements of a semigroup `S`

- `LPreorder.iff_in_leftIdeal` - `x` is in the principal Left Ideal of `y` iff `x ≤𝓛 y`.
- `RPreorder.iff_in_rightIdeal` - `x` is in the principal right ideal of `y` iff `x ≤𝓡 y`.
- `JPreorder.iff_in_ideal'` - `x` is in the principal Ideal of `y` iff `x ≤𝓙 y`.

- `LPreorder.le_in_leftIdeal` - if `x` is in a left Ideal and `y ≤𝓛 x`
then `y` is in the left ideal too.
- `RPreorder.le_in_rightIdeal` - if `x` is in a right Ideal and `y ≤𝓡 x`
then `y` is in that right ideal too.
- `JPreorder.le_in_ideal'` - if `x` is in an Ideal and `y ≤𝓙 x` then `y` is in that ideal too.

- `LPreorder.iff_leftIdeal_subset` - The principal left ideal of `x` is a subset of
that of `y` iff `x ≤𝓛 y`.
- `RPreorder.iff_rightIdeal_subset` - The principal right ideal of `x` is a subset of
that of `y` iff `x ≤𝓡 y`.
- `JPreorder.iff_ideal'_subset` - The principal ideal of `x` is a subset of
that of `y` iff `x ≤𝓡 y`.

- `LEquiv.iff_leftIdeal_eq` - The principal left ideal of `x` is equal to
that of `y` iff `x ≤𝓛 y`.
- `REquiv.iff_rightIdeal_eq` - The principal right ideal of `x` is equal to
that of `y` iff `x ≤𝓡 y`.
- `JEquiv.iff_ideal'_eq` - The principal ideal of `x` is equal to that of `y` iff `x ≤𝓡 y`.

- `SimpleSemigroup.ideal` - Given a `SimpleSemigroup` instance, all ideals are empty or full.
- `ZeroSimpleSemigroup.ideal` - Given a `ZeroSimpleSemigroup` instance, all ideals are empty,
full, or the zero ideal.

- `JEquiv.ofSimple` - Given a `SimpleSemigroup` instance, all elements are 𝓙-equivalent.
- `JPreorder.ofZeroSimple` - Given a `ZeroSimpleSemigroup` instance, all non-zero elements are
𝓙-preorder related.

- `RegularSemigroup.regular` - Given an instance of `RegularSemigroup`, for all `x` there exists
a `y` such that `x * y * x = x `


## Notation
- `⊤, ∅ or {} : Ideal' α` refer to the full and empty ideals, respectively.
- Given `[MulZeroClass α]`, `⊥` represents the left/right/two-sided ideal `{0}`

For `p, q : Ideal' α`:
- `p ∩ q : Ideal α` denotes their intersection.
- `p ≤ q` is notation for `(p : Set α) ⊆ (q : Set α)`

## Implementation Notes
The `SetLike` implementation is from the template in the docstring of `Mathlib.Data.Setlike.Basic`.

For an `p : Ideal' α` and `x : α`, the notation `x ∈ (p : Set S)` is perfered over `x ∈ p.carrier`
and this is supported by tagging the `mem_carrier` lemmas with `@[simp]`.

For principal ideals, use `Ideal'.ofSet {x}`.


## TODO

Prove that ideals are stable under surjective morphisms and inverses of morphisms
Prove that a semigroup has at most one minimal ideal
-/

open Pointwise -- Allows `s * t` notation for pointise set mul

/-- A Left Ideal is a set `X` such that `∀ y, ∀ x ∈ X, y * x ∈ X`. -/
structure LeftIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mul_mem_mem {x: α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace LeftIdeal

variable {α : Type*} [Mul α]

/-- `SetLike` instance requires we prove that there is an injection from `LeftIdeal → Set`.
It regesters a coersion to `Set` and provides various simp lemmas and instances. -/
instance : SetLike (LeftIdeal α) α :=
  ⟨LeftIdeal.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : LeftIdeal α} {x : α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

lemma mem_coe {p : LeftIdeal α} {x : α} : x ∈ (p : Set α) ↔ x ∈ p := Iff.rfl

/-- This allows us to use the `ext` tactic -/
@[ext] theorem ext {p q : LeftIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {p : LeftIdeal α} (hin : x ∈ p) : y * x ∈ p := by
  have h := p.mul_mem_mem hin y; simp_all

/-- Allows for notation `∅ : LeftIdeal α` for the empty ideal. -/
instance : EmptyCollection (LeftIdeal α) where
  emptyCollection := {
      carrier := ∅
      mul_mem_mem := by simp}

@[simp] lemma coe_empty : (({} : LeftIdeal α) : Set α) = {} := rfl

/-- Allows for notation `⊤ : LeftIdeal α` for the full ideal. -/
instance : Top (LeftIdeal α) where
  top := {
      carrier := Set.univ
      mul_mem_mem := by simp}

@[simp] lemma coe_top : ((⊤ : LeftIdeal α) : Set α) = Set.univ := rfl

/-- Allows for notation `⊥ : LeftIdeal α` for the left ideal `{0}`. -/
instance {β : Type*} [MulZeroClass β] : Bot (LeftIdeal β) where
  bot := {carrier := {0}
          mul_mem_mem := by simp
  }

@[simp] lemma coe_bot {β : Type*} [MulZeroClass β] : ((⊥ : LeftIdeal β) : Set β) = {0} := rfl

/-- The intersection of two left ideals is a left ideal. -/
instance : Inter (LeftIdeal α) where
  inter p q := {
    carrier := (p : Set α) ∩ (q : Set α)
    mul_mem_mem := by
      intros x hx y
      rcases hx with ⟨hxp, hxq⟩
      constructor
      · exact p.mul_mem_mem hxp y -- Proof for `y * x ∈ p.carrier`
      · exact q.mul_mem_mem hxq y -- Proof for `y * x ∈ q.carrier`
  }

@[simp] lemma inter_coe {p q : LeftIdeal α} : ((p ∩ q) : Set α) = (p : Set α) ∩ (q : Set α) := rfl

/-- If `p` is a left ideal of `α`, then `α * p ⊆ p`. -/
@[simp] lemma univ_mul_self_subset_self (p : LeftIdeal α) : (Set.univ : Set α) * p ⊆ p := by
  rintro x ⟨y, ⟨z, ⟨u, ⟨hu, h⟩⟩⟩⟩
  simp_all [← h]

variable {S : Type*} [Semigroup S]

/-- Given a set in a Semigroup, the minimal Left Ideal containing the set. -/
def ofSet (s : Set S) : LeftIdeal S where
  carrier := Set.univ * s ∪ s
  mul_mem_mem := by
    intros x hx y
    obtain ⟨w, ⟨_, ⟨z, ⟨hz, hx⟩⟩⟩⟩ | hx := hx
    · simp_all
      subst hx
      simp [← mul_assoc]
      left
      use y * w; simp
      use z
    · left
      use y; simp
      use x

lemma ofSet_def (p : Set S) : ↑(ofSet p) = Set.univ * p ∪ p := by rfl

@[simp] lemma mem_ofSet (p : Set S) (x : S) : x ∈ (ofSet p) ↔ x ∈ Set.univ * p ∪ p := by rfl

/-- For `q : Set S`, `LeftIdeal.ofSet q` is the minimal left ideal containing the set. -/
theorem ofSet_minimal {p : LeftIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  simp only [ ← SetLike.coe_subset_coe]
  intros x hx
  simp_all
  rcases hx with ⟨z, ⟨_, ⟨y, ⟨hy, hx⟩⟩⟩⟩ | hx
  · simp_all
    subst hx
    have hy' : y ∈ p := hin hy
    simp_all
  · apply hin hx

end LeftIdeal

/-- A right ideal is a set `X` such that `∀ y, ∀ x ∈ X, x * y ∈ X`. -/
structure RightIdeal (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x: α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier

namespace RightIdeal

variable {α : Type*} [Mul α]

instance : SetLike (RightIdeal α) α :=
  ⟨RightIdeal.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : RightIdeal α} {x : α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

lemma mem_coe {p : RightIdeal α} {x : α} : x ∈ (p : Set α) ↔ x ∈ p := Iff.rfl

@[ext] theorem ext {p q : RightIdeal α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

@[simp] lemma mem {x y : α} {p : RightIdeal α} (hin : x ∈ p) : x * y ∈ p := by
  have h := p.mem_mul_mem hin y; simp_all

instance : EmptyCollection (RightIdeal α) where
  emptyCollection := {
      carrier := ∅
      mem_mul_mem := by simp}

@[simp] lemma coe_empty : (({} : RightIdeal α) : Set α) = {} := rfl

instance : Top (RightIdeal α) where
  top := {carrier := Set.univ,
          mem_mul_mem := by simp_all}

@[simp] lemma coe_top : ((⊤ : RightIdeal α) : Set α) = Set.univ := rfl

instance {β : Type*} [MulZeroClass β] : Bot (RightIdeal β) where
  bot := {carrier := {0}
          mem_mul_mem := by simp
  }

@[simp] lemma coe_bot {β : Type*} [MulZeroClass β] : ((⊥ : RightIdeal β) : Set β) = {0} := rfl

/-- The intersection of right ideals is a right isimpdeal. -/
instance : Inter (RightIdeal α) where
  inter p q := {
    carrier := (p : Set α) ∩ (q : Set α)
    mem_mul_mem := by
      intros x hx y
      rcases hx with ⟨hxp, hxq⟩
      constructor
      · exact p.mem_mul_mem hxp y -- Proof for `x * y ∈ p.carrier`
      · exact q.mem_mul_mem hxq y -- Proof for `x * y ∈ q.carrier`
  }

@[simp] lemma inter_coe {p q : RightIdeal α} : ((p ∩ q) : Set α) = (p : Set α) ∩ (q : Set α) := rfl

/-- If `p` is a right ideal of `α`, then `p * α ⊆ p`. -/
@[simp] lemma mul_univ_subset_self (p : RightIdeal α) : p * (Set.univ : Set α) ⊆ p := by
  rintro x ⟨y, ⟨z, ⟨u, ⟨hu, h⟩⟩⟩⟩
  simp_all [← h]

variable {S : Type*} [Semigroup S]

/-- Given a set in a Semigroup, the minimal right ideal containing the set. -/
def ofSet (s : Set S) : RightIdeal S where
  carrier := s * Set.univ ∪ s
  mem_mul_mem := by
    intros x hx y
    obtain ⟨w, ⟨hw, ⟨z, ⟨hz, hx⟩⟩⟩⟩ | hx := hx
    · simp_all
      subst hx
      left
      use w; simp_all
      use z * y
      simp_all [mul_assoc]
    · left
      use x; simp_all

lemma ofSet_def (p : Set S) : ↑(ofSet p) = p * Set.univ ∪ p := by rfl

@[simp] lemma mem_ofSet (p : Set S) (x : S) : x ∈ (ofSet p) ↔ x ∈ p * Set.univ ∪ p := by rfl

/-- For `q : Set S`, `RightIdeal.ofSet q` is the minimal right ideal containing the set. -/
theorem ofSet_minimal {p : RightIdeal S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  simp only [ ← SetLike.coe_subset_coe]
  intros x hx
  simp_all
  rcases hx with ⟨z, ⟨hz, ⟨y, ⟨hy, hx⟩⟩⟩⟩ | hx
  · simp_all
    subst hx
    have hz : z ∈ p := hin hz
    simp_all
  · apply hin hx

end RightIdeal

/-- An ideal is a set closed under multiplication on both sides. -/
structure Ideal' (α : Type*) [Mul α] where
  carrier : Set α
  mem_mul_mem {x: α} (hin : x ∈ carrier) (y : α) : x * y ∈ carrier
  mul_mem_mem {x: α} (hin : x ∈ carrier) (y : α) : y * x ∈ carrier

namespace Ideal'

variable {α : Type*} [Mul α]

def toLeftIdeal (p : Ideal' α) : LeftIdeal α where
  carrier := p.carrier
  mul_mem_mem := p.mul_mem_mem


def toRightIdeal (p : Ideal' α) : RightIdeal α where
  carrier := p.carrier
  mem_mul_mem := p.mem_mul_mem

instance : SetLike (Ideal' α) α :=
  ⟨Ideal'.carrier, fun p q h ↦ by cases p; cases q; congr!⟩

@[simp] lemma mem_carrier {p : Ideal' α} {x : α} : x ∈ p.carrier ↔ x ∈ (p : Set α) := Iff.rfl

lemma mem_coe {p : Ideal' α} {x : α} : x ∈ (p : Set α) ↔ x ∈ p := Iff.rfl

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

instance : EmptyCollection (Ideal' α) where
  emptyCollection := {
      carrier := ∅
      mem_mul_mem := by simp
      mul_mem_mem := by simp}

@[simp] lemma coe_empty : ((∅ : Ideal' α) : Set α) = {} := rfl

@[simp] lemma not_in_empty (x : α) : x ∉ (∅ : Ideal' α) := by
  intros h
  rw [← mem_coe] at h
  simp_all

instance : Top (Ideal' α) where
  top := {carrier := Set.univ,
          mem_mul_mem := by simp_all,
          mul_mem_mem := by simp_all}

@[simp] lemma coe_top : ((⊤ : Ideal' α) : Set α) = Set.univ := rfl

@[simp] lemma in_top (x : α) : x ∈ (⊤ : Ideal' α) := by
  simp_all [← mem_coe]

instance {β : Type*} [MulZeroClass β] : Bot (Ideal' β) where
  bot := {carrier := {0}
          mem_mul_mem := by simp
          mul_mem_mem := by simp
  }

@[simp] lemma coe_bot {β : Type*} [MulZeroClass β] : ((⊥ : Ideal' β) : Set β) = {0} := rfl

lemma eq_zero_iff_in_bot [MulZeroClass β] (x : β) : x = 0 ↔ x ∈ (⊥ : Ideal' β) := by
  rw [← mem_coe]
  simp

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

@[simp] lemma inter_coe {p q : Ideal' α} : ((p ∩ q) : Set α) = (p : Set α) ∩ (q : Set α) := rfl

variable {S : Type*} [Semigroup S]

/-- Given a set in a Semigroup, the minimal ideal containing the set. -/
def ofSet (s : Set S) : Ideal' S where
  carrier := LeftIdeal.ofSet s ∪ RightIdeal.ofSet s ∪ Set.univ * s * Set.univ ∪ s
  mem_mul_mem := by
    intros x hx y
    rcases hx with ⟨⟨hx | hx⟩ | hx⟩ | hx
    · simp_all
      rcases hx with ⟨w, ⟨hw, ⟨z, ⟨hz, hx⟩⟩⟩⟩ | hx
      · simp_all
        subst hx
        left; right
        use w * z; simp_all
        use w; simp
        use z
      · left; left; right; left
        use x; simp_all
    · simp_all
    · rcases hx with ⟨w, ⟨hw, ⟨z, ⟨hz, hx⟩⟩⟩⟩
      simp_all
      subst hx
      left; right
      use w; simp_all
      use z * y; simp_all [mul_assoc]
    · simp_all
  mul_mem_mem := by
    intros x hx y
    rcases hx with ⟨⟨hx | hx⟩ | hx⟩ | hx
    · simp_all
    · simp_all
      rcases hx with ⟨w, ⟨hw, ⟨z, ⟨hz, hx⟩⟩⟩⟩ | hx
      · simp_all
        subst hx
        left; right
        simp [← mul_assoc]
        use y * w; simp_all
        use y; simp
        use w
      · left; left; left; left
        use y; simp
        use x
    · rcases hx with ⟨w, ⟨⟨z, ⟨hz, ⟨u, ⟨hu, hu'⟩⟩⟩⟩, ⟨v, ⟨_, hv⟩⟩⟩⟩
      simp_all
      subst hu'
      subst hv
      left; right
      simp [← mul_assoc]
      use y * z* u; simp_all
      use y * z; simp_all
      use u
    · simp_all

lemma ofSet_def (p : Set S) : ↑(ofSet p) =
    (LeftIdeal.ofSet p ∪ RightIdeal.ofSet p ∪ Set.univ * p * Set.univ ∪ p : Set S) := by rfl

@[simp] lemma mem_ofSet (s : Set S) (x : S) : x ∈ (ofSet s) ↔
    x ∈ (LeftIdeal.ofSet s ∪ RightIdeal.ofSet s ∪ Set.univ * s * Set.univ ∪ s : Set S) := by rfl

/-- For `q : Set S`, `Ideal'.ofSet q` is the minimal ideal containing the set. -/
theorem ofSet_minimal {p : Ideal' S} {q : Set S} (hin : q ⊆ ↑p) :
    (ofSet q) ≤ p := by
  simp only [ ← SetLike.coe_subset_coe]
  intros x hx
  simp_all
  rcases hx with (((hx | hx) | (hx | hx)) | hx) | hx
  · rcases hx with ⟨y, ⟨_, ⟨z, ⟨hz, hx⟩⟩⟩⟩
    simp_all
    subst x
    have hz' : z ∈ p := hin hz
    simp_all
  · exact hin hx
  · rcases hx with ⟨y, ⟨hy, ⟨z, ⟨_, hx⟩⟩⟩⟩
    simp_all
    subst hx
    have hy' : y ∈ p := hin hy
    simp_all
  · exact hin hx
  · rcases hx with ⟨z, ⟨⟨w, ⟨hw, ⟨v, ⟨hv, hz⟩⟩⟩⟩, ⟨y, ⟨_, ⟨u, hu⟩⟩⟩⟩⟩
    simp_all
    subst hz
    have hv' : v ∈ p := hin hv
    simp_all
  · exact hin hx

end Ideal'

/-!
### Ideal characterization of Greens Relations
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] (x y : S)

/-- `x` is in the principal left ideal of `y` iff `x ≤𝓛 y`. -/
lemma LPreorder.iff_in_leftIdeal : x ∈ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by
  simp_all
  constructor
  · intro h
    rcases h with heq | ⟨z, hz⟩
    · subst heq; simp
    · use z; simp_all [← WithOne.coe_mul]
  · intro h
    obtain ⟨w, hw⟩ := h
    cases w with
    | one => simp_all
    | coe w =>
      right
      simp_all [← WithOne.coe_mul]
      use w

/-- For `x ∈ i : LeftIdeal S`, if `y ≤𝓛 x` then `y ∈ i`. -/
lemma LPreorder.le_in_leftIdeal {x y : S} {i : LeftIdeal S} (hx : x ∈ i) (hy : y ≤𝓛 x) :
    y ∈ i := by
  obtain ⟨z, hz⟩ := hy
  cases z with
  | one => simp_all
  | coe z =>
    simp_all [← WithOne.coe_mul]
    subst y
    simp_all

/-- The principal left ideal of `x` is a subset of that of `y` iff `x ≤𝓛 y` -/
theorem LPreorder.iff_leftIdeal_subset : LeftIdeal.ofSet {x} ≤ LeftIdeal.ofSet {y} ↔ x ≤𝓛 y := by
  constructor
  · rintro h
    rw [← LPreorder.iff_in_leftIdeal]
    apply h
    simp
  · rintro ⟨z, hz⟩
    cases z with
    | one => simp_all
    | coe z =>
      intros w hw
      rw [LPreorder.iff_in_leftIdeal] at hw ⊢
      simp_all [← WithOne.coe_mul]
      subst x
      apply LPreorder.trans hw
      simp

/-- The principal left ideal of `x` is a equal to that of `y` iff `x 𝓛 y`. -/
theorem LEquiv.iff_leftIdeal_eq : LeftIdeal.ofSet {x} = LeftIdeal.ofSet {y} ↔ x 𝓛 y := by
  constructor
  · intro h
    constructor <;> rw [← LPreorder.iff_leftIdeal_subset, h]
  · rintro ⟨hr, hl⟩
    simp_all [← LPreorder.iff_leftIdeal_subset]
    ext z
    constructor
    · intros h
      exact hr h
    · intros h
      exact hl h

/-- `x` is in the principal right ideal of `y` iff `x ≤𝓡 y`. -/
lemma RPreorder.iff_in_rightIdeal : x ∈ RightIdeal.ofSet {y} ↔ x ≤𝓡 y := by
  simp_all
  constructor
  · intro h
    rcases h with heq | ⟨z, hz⟩
    · subst heq; simp
    · use z; simp_all [← WithOne.coe_mul]
  · intro h
    obtain ⟨w, hw⟩ := h
    cases w with
    | one => simp_all
    | coe w =>
      right
      simp_all [← WithOne.coe_mul]
      use w

/-- For `x ∈ i : RightIdeal S`, if `y ≤𝓡 x` then `y ∈ i`. -/
lemma RPreorder.le_in_rightIdeal {x y : S} {i : RightIdeal S} (hx : x ∈ i) (hy : y ≤𝓡 x) :
    y ∈ i := by
  obtain ⟨z, hz⟩ := hy
  cases z with
  | one => simp_all
  | coe z =>
    simp_all [← WithOne.coe_mul]
    subst y
    simp_all

/-- The principal right ideal of `x` is a subset of that of `y` iff `x ≤𝓡 y` -/
theorem RPreorder.iff_rightIdeal_subset : RightIdeal.ofSet {x} ≤ RightIdeal.ofSet {y} ↔ x ≤𝓡 y := by
  constructor
  · rintro h
    rw [← RPreorder.iff_in_rightIdeal]
    apply h
    simp
  · rintro ⟨z, hz⟩
    cases z with
    | one => simp_all
    | coe z =>
      intros w hw
      rw [RPreorder.iff_in_rightIdeal] at hw ⊢
      simp_all [← WithOne.coe_mul]
      subst x
      apply RPreorder.trans hw
      simp

/-- The principal right ideal of `x` is a equal to that of `y` iff `x 𝓡 y`. -/
theorem REquiv.iff_rightIdeal_eq : RightIdeal.ofSet {x} = RightIdeal.ofSet {y} ↔ x 𝓡 y := by
  constructor
  · intro h
    constructor <;> rw [← RPreorder.iff_rightIdeal_subset, h]
  · rintro ⟨hr, hl⟩
    simp_all [← RPreorder.iff_rightIdeal_subset]
    ext z
    constructor
    · intros h
      exact hr h
    · intros h
      exact hl h

/-- `x` is in the principal ideal of `y` iff `x ≤𝓙 y`. -/
lemma JPreorder.iff_in_ideal' : x ∈ Ideal'.ofSet {y} ↔ x ≤𝓙 y := by
  simp_all
  constructor
  · intro h
    rcases h with ((h | ⟨z, hz⟩) | (⟨z, hz⟩ | ⟨z, hz⟩)) | h
    · simp_all
    · apply LPreorder.to_jPreorder
      use z
      simp_all [← WithOne.coe_mul]
    · simp
    · apply RPreorder.to_jPreorder
      use z
      simp_all [← WithOne.coe_mul]
    · rcases h with ⟨w, ⟨⟨u, hu⟩, ⟨z, ⟨_, hz⟩⟩⟩⟩
      simp_all
      subst x
      subst w
      simp
  · intro h
    obtain ⟨w, ⟨v, hv⟩⟩ := h
    cases w with
    | one =>
       cases v with
       | one => simp_all
       | coe v =>
         simp_all [← WithOne.coe_mul]
         subst x
         simp_all
    | coe w =>
      cases v with
      | one =>
        simp_all [← WithOne.coe_mul]
        subst x
        simp_all
      | coe v =>
        simp_all [← WithOne.coe_mul]
        subst x
        right
        use w * y
        simp_all

/-- For `x ∈ i : Ideal' S`, if `y ≤𝓙 x` then `y ∈ i`. -/
lemma JPreorder.le_in_ideal' {x y : S} {i : Ideal' S} (hx : x ∈ i) (hy : y ≤𝓙 x) : y ∈ i := by
  obtain ⟨z, v, hy⟩ := hy
  cases z with
  | one =>
    cases v with
    | one => simp_all
    | coe v =>
      simp_all [← WithOne.coe_mul]
      subst y
      simp_all
  | coe z =>
    cases v with
    | one =>
      simp_all [← WithOne.coe_mul]
      subst y
      simp_all
    | coe v =>
      simp_all [← WithOne.coe_mul]
      subst y
      simp_all

/-- The principal ideal of `x` is a subset of that of `y` iff `x ≤𝓙 y` -/
theorem JPreorder.iff_ideal'_subset : Ideal'.ofSet {x} ≤ Ideal'.ofSet {y} ↔ x ≤𝓙 y := by
  constructor
  · intros h
    rw [← JPreorder.iff_in_ideal']
    apply h
    simp
  · rintro ⟨w, v, hx⟩
    cases w with
    | one =>
      simp_all
      cases v with
      | one => simp_all
      | coe v =>
        simp_all [← WithOne.coe_mul]
        subst x
        intros z hz
        rw [JPreorder.iff_in_ideal'] at hz ⊢
        apply JPreorder.trans hz
        simp_all
    | coe w =>
      cases v with
      | one =>
        simp_all [← WithOne.coe_mul]
        subst x
        intros x hx
        rw [JPreorder.iff_in_ideal'] at hx ⊢
        apply JPreorder.trans hx
        simp_all
      | coe v =>
        simp_all [← WithOne.coe_mul]
        subst x
        intros x hx
        rw [JPreorder.iff_in_ideal'] at hx ⊢
        apply JPreorder.trans hx
        simp_all

/-- The principal ideal of `x` is a equal to that of `y` iff `x 𝓙 y`. -/
theorem JEquiv.ideal'_eq : Ideal'.ofSet {x} = Ideal'.ofSet {y} ↔ x 𝓙 y := by
  constructor
  · intro h
    constructor <;> rw [← JPreorder.iff_ideal'_subset, h]
  · rintro ⟨hr, hl⟩
    simp_all [← JPreorder.iff_ideal'_subset]
    ext z
    constructor
    · intros h
      exact hr h
    · intros h
      exact hl h

end Semigroup

/-!
### Simple Semigroups
-/

/-- A semigroup is simple if its only ideals are `⊥` and `∅` -/
class SimpleSemigroup (S : Type*) extends Semigroup S where
  ideal_eq : ∀ (I : Ideal' S), I = ∅ ∨ I = ⊤

variable {S : Type*}

@[simp] lemma SimpleSemigroup.ideal [inst : SimpleSemigroup S] (I : Ideal' S) :
    I = ∅ ∨ I = ⊤ := inst.ideal_eq I

class ZeroSimpleSemigroup (S : Type*) extends SemigroupWithZero S where
  ideal_eq : ∀ (I : Ideal' S), I = ∅ ∨ I = ⊤ ∨ I = ⊥

@[simp] lemma ZeroSimpleSemigroup.ideal [inst : ZeroSimpleSemigroup S] (I : Ideal' S) :
    I = ∅ ∨ I = ⊤ ∨ I = ⊥ := inst.ideal_eq I

namespace Semigroup

/-- In a simple semigroup, all elements are J-preorder related -/
lemma JPreorder.ofSimple [SimpleSemigroup S] (x y : S) :  x ≤𝓙 y := by
  have hx := SimpleSemigroup.ideal (Ideal'.ofSet {x})
  have hy := SimpleSemigroup.ideal (Ideal'.ofSet {y})
  rw [← JPreorder.iff_ideal'_subset]
  rcases hx with he | ht
  · have hc : x ∈ Ideal'.ofSet {x} := by simp
    rw [he] at hc
    contradiction
  · rcases hy with he' | ht'
    · have hc : y ∈ Ideal'.ofSet {y} := by simp
      simp_all
    · simp_all

/-- In a simple semigroup, all elements are 𝓙 related -/
theorem JEquiv.ofSimple [SimpleSemigroup S] (x y : S) :  x 𝓙 y :=
  ⟨JPreorder.ofSimple x y, JPreorder.ofSimple y x⟩

/-- If all elements of a semigroup are J-preorder related, then it is a simple semigroup. -/
instance JPreorder.toSimpleSemigroup [Semigroup S] (h : ∀ x y : S, x ≤𝓙 y) : SimpleSemigroup S where
  ideal_eq (i : Ideal' S) := by
    have he := isEmpty_or_nonempty i
    rcases he with he | hne
    · left
      have h₂ := Set.eq_empty_of_isEmpty (i : Set S)
      ext y
      rw [← Ideal'.mem_coe, h₂]
      rfl
    · rcases hne with w
      obtain ⟨x, hx⟩ := hne
      right
      ext y
      simp_all
      apply JPreorder.le_in_ideal' hx
      apply h

/-- All non-zero elements of a zero-simple-semigroup are J-preorder related. -/
lemma JPreorder.ofZeroSimple [ZeroSimpleSemigroup S] (x y : S) (hy : y ≠ 0) : x ≤𝓙 y := by
  rw [← JPreorder.iff_ideal'_subset]
  have hix := ZeroSimpleSemigroup.ideal (Ideal'.ofSet {x})
  have hiy := ZeroSimpleSemigroup.ideal (Ideal'.ofSet {y})
  rcases hix with hix | (hix | hix)
  <;> rcases hiy with hiy | (hiy | hiy)
  <;> simp_all
  <;> intros z hz
  <;> simp_all
  <;> have hy' : y ∈ Ideal'.ofSet {y} := by simp;
  <;> rw [hiy] at hy'
  <;> contradiction

/-- If all non-zero elements of a semigroup with zero are J-preorder related, then it is a
zero-simple semigroup. -/
instance JPreorder.toZeroSimpleSemigroup [SemigroupWithZero S] (h : ∀ x y : S, y ≠ 0 → x ≤𝓙 y) :
    ZeroSimpleSemigroup S where
  ideal_eq (i : Ideal' S) := by
    have he := isEmpty_or_nonempty i
    rcases he with he | hne
    · left
      have h₂ := Set.eq_empty_of_isEmpty (i : Set S)
      ext y
      rw [← Ideal'.mem_coe, h₂]
      rfl
    · rcases hne with w
      obtain ⟨x, hx⟩ := hne
      right
      have h0 := eq_zero_or_neZero x
      rcases h0 with h0 | hne0
      · subst x
        have he' := isEmpty_or_nonempty {y : S | y ∈ i ∧ y ≠ 0}
        rcases he' with he | he
        · simp_all
          right
          ext y
          constructor
          · intros hy
            simp [← Ideal'.eq_zero_iff_in_bot]
            by_contra hyne
            apply he.false ⟨y, ⟨hy, hyne⟩⟩
          · intros hy
            simp_all [← Ideal'.eq_zero_iff_in_bot]
        · left
          obtain ⟨y, hy⟩ := he
          simp_all
          rcases hy with ⟨hy₁, hy₂⟩
          ext x
          simp_all
          specialize h x y hy₂
          apply JPreorder.le_in_ideal' hy₁ h
      · left
        ext y
        simp_all
        apply JPreorder.le_in_ideal' hx
        apply h
        exact hne0.out

/-!
### Regular Semigroups

See `Semigroup.DEquiv.regular_d_class_tfae` and `regularClass_iff_*` / `hasIdempotent_iff_*` in
`MyProject/Green/Location.lean` (Proposition 1.9).
-/

section Regular

/-- A element `x` of a magma is regular iff `∃ y, x * y * x = x`. -/
def isRegularElem {α : Type*} [Mul α] (x : α) : Prop :=
  ∃ y : α, x * y * x = x

/-- In a regular semigroup, every element is regular. -/
class RegularSemigroup (S : Type*) extends Semigroup S where
  isRegular : ∀ x : S, isRegularElem x

@[simp] lemma RegularSemigroup.regular [inst : RegularSemigroup S] (x : S) :
    ∃ y : S, x * y * x = x := inst.isRegular x

end Regular

end Semigroup
