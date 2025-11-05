import Mathlib.Data.Set.Function
import MyProject.Green.Basic

/-!
# Green's Lemma

This file proves Green's lemma, which is the following:
Let `x 𝓡 y` such that `x = y * u` and `y = x * v`.
Then the map `x ↦ x * v` is a bijection from the 𝓛-class of `x` to the 𝓛-class of `y`,
and the map `x → x * u` is its inverse. Additionally, these bijections preserve 𝓗 classes.

We also prove the dual version of this lemma.

## Main Theorems

Let `x 𝓡 y` such that `x = y * u` and `y = x * v`.

* `REquiv.inv_on_lClass` - the map `x ↦ x * u` is the inverse of `x ↦ x * v` on the 𝓛-class of `x`.
* `REquiv.bij_on_lClass` - the map `x ↦ x * v` is a bijection from the
𝓛-class of `x` to the 𝓛-class of `y`.
* `REquiv.bij_on_lClass_pres_hClass` - this bijection preserves 𝓗 classes.

Let `x 𝓛 y` such that `x = u * y` and `y = v * x`.

* `LEquiv.inv_on_rClass` - the map `x ↦ v * x` is the inverse of `x ↦ u * x` on the 𝓡-class of `x`.
* `LEquiv.bij_on_rClass` - the map `x ↦ u * x` is a bijection from the
𝓡-class of `x` to the 𝓡-class of `y`.
* `LEquiv.bij_on_rClass_pres_hClass` - this bijection preserves 𝓗 classes.

## References

TODO

## Blueprint

* One lemma entry for the 𝓡-class bijection and its properties.
label : greens-lemma
dependencies : todo
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] {x y u v w : S}

/-- If `x 𝓡 y` such that `x = y * u` and `y = x * v`, then right translation by `v * u` on any
element 𝓛-equivalent to `x` is the idenity. -/
lemma REquiv.translation_id (hx : x = y * u) (hy : y = x * v) (hw : x 𝓛 w) : w * v * u = w := by
  rcases hw with ⟨_, ⟨z, hz⟩⟩
  cases z with
  | one => simp at hz; subst hz; rw [← hy, hx]
  | coe z =>
    simp [← WithOne.coe_mul] at hz
    subst hz
    rw [mul_assoc z, ← hy, mul_assoc, ← hx]

/-- If `y ≤𝓡 x` such that `y = x * v`, then the map `w ↦ w * v`
maps the 𝓛-class of `x` to that of `y` -/
lemma REquiv.map_on_lClass (hy : y = x * v) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp [Set.MapsTo]
  intros z hz
  rw [hy]
  apply LEquiv.rmult_compat
  exact hz

/-- If `x 𝓡 y` such that `x = y * u` and `y = x * v`, then the map `w ↦ w * u` is injective on the
𝓛-class of `x`. -/
lemma REquiv.inj_on_lClass (hx : x = y * u) (hy : y = x * v) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓛 := by
  simp [Set.InjOn]
  intros w hw z hz heq
  have hw₂ := REquiv.translation_id hx hy hw.symm
  have hz₂ := REquiv.translation_id hx hy hz.symm
  rw [← hw₂, ← hz₂, heq]

/-- If `x 𝓡 y` such that `x = y * u` and `y = x * v`, then the map `w ↦ w * u` is surjective
from the 𝓛-class of `x` to that of `y`. -/
lemma REquiv.surj_on_lClass (hx : x = y * u) (hy : y = x * v) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp [Set.SurjOn]
  intros z hz
  simp at hz ⊢
  use z * u
  constructor
  · rw [hx]
    apply LEquiv.rmult_compat
    exact hz
  · have hl : y 𝓛 y := by simp
    apply REquiv.translation_id hy hx hz.symm

/-- If `x 𝓡 y` such that `x = y * u` and `y = x * v`, then the map `w ↦ w * u` is the inverse of
`w ↦ w * v` when restricted to the 𝓛-classes of `x` and `y` -/
theorem REquiv.inv_on_lClass (hx : x = y * u) (hy : y = x * v) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp [Set.InvOn, Set.LeftInvOn]
  constructor
  · intro z hz
    apply REquiv.translation_id hx hy hz.symm
  · intro z hz
    apply REquiv.translation_id hy hx hz.symm

/-- If `x 𝓡 y` such that `x = y * u` and `y = x * v`, then the map `w ↦ w * v` is a bijection from
the 𝓛-class of `x` to that of `y`. -/
theorem REquiv.bij_on_lClass (hx : x = y * u) (hy : y = x * v) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · apply REquiv.map_on_lClass hy
  · apply REquiv.inj_on_lClass hx hy
  · apply REquiv.surj_on_lClass hx hy

/-- If `x 𝓡 y` such that `x = y * u` and `y = x * v`,
then the map `w ↦ w * v` preserves 𝓗-classes. -/
theorem REquiv.bij_on_lClass_pres_hClass (hx : x = y * u) (hy : y = x * v)
  (hw : x 𝓛 w) (hz : x 𝓛 z) : w 𝓗 z ↔ w * v 𝓗 z * v := by
  constructor
  · intro h
    rw [HEquiv.iff_rEquiv_and_lEquiv] at h ⊢
    constructor
    · rcases h with ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, _⟩
      constructor
      · use u * a * v
        have hz₂ : ↑z * ↑v * ↑u = (↑z : WithOne S) := by
          simp [← WithOne.coe_mul]
          exact REquiv.translation_id hx hy hz
        simp [← mul_assoc]
        rw [hz₂, ← ha]
      · use u * b * v
        have hw₂ : ↑w * ↑v * ↑u = (↑w : WithOne S) := by
          simp [← WithOne.coe_mul]
          exact REquiv.translation_id hx hy hw
        simp [← mul_assoc]
        rw [hw₂, ← hb]
    · apply LEquiv.rmult_compat w z v h.2
  · intros h
    rw [HEquiv.iff_rEquiv_and_lEquiv]
    constructor
    · have hr₁ : w 𝓡  w * v := by
        simp [REquiv]
        use u
        have hw₂ := REquiv.translation_id hx hy hw
        simp [← WithOne.coe_mul]
        symm
        apply hw₂
      rw [HEquiv.iff_rEquiv_and_lEquiv] at h
      have hr₂ : w * v 𝓡 z * v := h.1
      have hr₃ : w 𝓡 z * v := REquiv.trans hr₁ hr₂
      have hr₄ : z * v 𝓡 z := by
        simp [REquiv]
        use u
        have hz₂ := REquiv.translation_id hx hy hz
        simp [← WithOne.coe_mul]
        symm
        apply hz₂
      apply REquiv.trans hr₃ hr₄
    · apply LEquiv.trans hw.symm hz

/-! ### Dual proofs -/

/-- If `x 𝓛 y` such that `x = u * y` and `y = v * x`, then left translation by `u * v` on any
element 𝓡-equivalent to `x` is the identity. -/
lemma LEquiv.translation_id (hx : x = u * y) (hy : y = v * x) (hw : x 𝓡 w) : u * v * w = w := by
  rcases hw with ⟨_, ⟨z, hz⟩⟩
  cases z with
  | one =>
    simp at hz
    subst hz
    rw [mul_assoc, ← hy, hx]
  | coe z =>
    simp [← WithOne.coe_mul] at hz
    subst hz
    rw [← mul_assoc, mul_assoc u, ← hy, ← hx]

/-- If `y ≤𝓛 x` such that `y = v * x`, then the map `w ↦ v * w`
maps the 𝓡-class of `x` to that of `y` -/
lemma LEquiv.map_on_rClass (hy : y = v * x) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp [Set.MapsTo]
  intros z hz
  rw [hy]
  apply REquiv.lmult_compat
  exact hz

/-- If `x 𝓛 y` such that `x = u * y` and `y = v * x`, then the map `w ↦ v * w` is injective on the
𝓡-class of `x`. -/
lemma LEquiv.inj_on_rClass (hx : x = u * y) (hy : y = v * x) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓡 := by
  simp [Set.InjOn]
  intros w hw z hz heq
  have hw₂ := LEquiv.translation_id hx hy hw.symm
  have hz₂ := LEquiv.translation_id hx hy hz.symm
  rw [← hw₂, ← hz₂]
  simp [mul_assoc, heq]

/-- If `x 𝓛 y` such that `x = u * y` and `y = v * x`, then the map `w ↦ v * w` is surjective
from the 𝓡-class of `x` to that of `y`. -/
lemma LEquiv.surj_on_rClass (hx : x = u * y) (hy : y = v * x) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp [Set.SurjOn]
  intros z hz
  simp at hz ⊢
  use u * z
  constructor
  · rw [hx]
    apply REquiv.lmult_compat
    exact hz
  · have hr : y 𝓡 y := by simp
    rw [← mul_assoc]
    apply LEquiv.translation_id hy hx hz.symm

/-- If `x 𝓛 y` such that `x = u * y` and `y = v * x`, then the map `w ↦ u * w` is the inverse of
`w ↦ v * w` when restricted to the 𝓡-classes of `x` and `y` -/
theorem LEquiv.inv_on_rClass (hx : x = u * y) (hy : y = v * x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp [Set.InvOn, Set.LeftInvOn]
  constructor
  · intro z hz
    rw [← mul_assoc]
    apply LEquiv.translation_id hx hy hz.symm
  · intro z hz
    rw [← mul_assoc]
    apply LEquiv.translation_id hy hx hz.symm

/-- If `x 𝓛 y` such that `x = u * y` and `y = v * x`, then the map `w ↦ v * w` is a bijection from
the 𝓡-class of `x` to that of `y`. -/
theorem LEquiv.bij_on_rClass (hx : x = u * y) (hy : y = v * x) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · apply LEquiv.map_on_rClass hy
  · apply LEquiv.inj_on_rClass hx hy
  · apply LEquiv.surj_on_rClass hx hy

/-- If `x 𝓛 y` such that `x = u * y` and `y = v * x`,
then the map `w ↦ v * w` preserves 𝓗-classes. -/
theorem LEquiv.bij_on_rClass_pres_hClass (hx : x = u * y) (hy : y = v * x)
  (hw : x 𝓡 w) (hz : x 𝓡 z) : w 𝓗 z ↔ v * w 𝓗 v * z := by
  constructor
  · intro h
    rw [HEquiv.iff_rEquiv_and_lEquiv] at h ⊢
    constructor
    · apply REquiv.lmult_compat w z v h.1
    · rcases h with ⟨_, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩⟩
      constructor
      · use v * a * u
        have hz₂ : ↑u * ↑v * ↑z = (↑z : WithOne S) := by
          simp [← WithOne.coe_mul]
          exact LEquiv.translation_id hx hy hz
        simp
        rw [mul_assoc]
        conv => rhs; rhs; rw [← mul_assoc, hz₂]
        rw [ha, mul_assoc]
      · use v * b * u
        have hw₂ : ↑u * ↑v * ↑w = (↑w : WithOne S) := by
          simp [← WithOne.coe_mul]
          exact LEquiv.translation_id hx hy hw
        simp
        rw [mul_assoc]
        conv => rhs; rhs; rw [← mul_assoc, hw₂]
        rw [hb, mul_assoc]
  · intros h
    rw [HEquiv.iff_rEquiv_and_lEquiv]
    constructor
    · apply REquiv.trans hw.symm hz
    · have hl₁ : w 𝓛 v * w := by
        simp [LEquiv]
        use u
        have hw₂ := LEquiv.translation_id hx hy hw
        simp [← WithOne.coe_mul]
        symm
        rw [← mul_assoc]
        apply hw₂
      rw [HEquiv.iff_rEquiv_and_lEquiv] at h
      have hl₂ : v * w 𝓛 v * z := h.2
      have hl₃ : w 𝓛 v * z := LEquiv.trans hl₁ hl₂
      have hl₄ : v * z 𝓛 z := by
        simp [LEquiv]
        use u
        have hz₂ := LEquiv.translation_id hx hy hz
        simp [← WithOne.coe_mul]
        symm
        rw [← mul_assoc]
        apply hz₂
      apply LEquiv.trans hl₃ hl₄

end Semigroup
