import Mathlib.Data.Set.Function
import MyProject.Green.Basic

/-!
# Green's Lemma

This file proves Green's lemma, which is the following:
Let `x 𝓡 y` such that `y * u = x` and `x * v = y`.
Then the map `x ↦ x * v` is a bijection from the 𝓛-class of `x` to the 𝓛-class of `y`,
and the map `x → x * u` is its inverse. Additionally, these bijections preserve 𝓗 classes.

We also prove the dual version of this lemma.

## Main Theorems

Let `x 𝓡 y` such that `y * u = x` and `x * v = y`.

* `REquiv.invOn_lClass` - the map `x ↦ x * u` is the inverse of `x ↦ x * v` on the 𝓛-class of `x`.
* `REquiv.bijOn_lClass` - the map `x ↦ x * v` is a bijection from the
𝓛-class of `x` to the 𝓛-class of `y`.
* `REquiv.bijOn_lClass_pres_hClass` - this bijection preserves 𝓗 classes.

Let `x 𝓛 y` such that `u * y = x` and `v * x = y`.

* `LEquiv.invOn_rClass` - the map `x ↦ u * x` is the inverse of `x ↦ v * x` on the 𝓡-class of `x`.
* `LEquiv.bijOn_rClass` - the map `x ↦ v * x` is a bijection from the
𝓡-class of `x` to the 𝓡-class of `y`.
* `LEquiv.bijOn_rClass_pres_hClass` - this bijection preserves 𝓗 classes.

## References

TODO

## Blueprint

* One lemma entry for the 𝓡-class bijection and its properties.
label : greens-lemma
dependencies : todo
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] {x y u v w : S}

/-- If `x 𝓡 y` such that `x * v = y` and `y * u = x`, then right translation by `v * u` on any
element 𝓛-equivalent to `x` is the identity. -/
lemma REquiv.translation_id (hv : x * v = y) (hu : y * u = x) (hw : w 𝓛 x) : w * v * u = w := by
  rcases hw.le with ⟨z, hz⟩
  cases z with
  | one => simp at hz; subst hz; rw [hv, hu]
  | coe z =>
    simp [← WithOne.coe_mul] at hz
    subst hz
    rw [mul_assoc z, hv, mul_assoc, hu]

/-- If `x * v = y`, then the map `w ↦ w * v`
maps the 𝓛-class of `x` to that of `y` -/
lemma RPreorder.mapsTo_lClass (hv : x * v = y) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp [Set.MapsTo]
  intros z hz
  rw [← hv]
  apply LEquiv.rmult_compat
  exact hz

/-- If `x 𝓡 y` such that `x * v = y` then the map `w ↦ w * v` is injective on the
𝓛-class of `x`. -/
lemma REquiv.injOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓛 := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one => -- trivial case, x = y
    simp at hu; subst hu
    intros w hw z hz heq
    simp at hw hz heq
    rw [← WithOne.coe_inj] at heq ⊢ hv
    simp at heq hv
    obtain ⟨a, ha⟩ := hw.le
    obtain ⟨b, hb⟩ := hz.le
    rwa [← ha, ← hb, mul_assoc, mul_assoc, hv, ha, hb] at heq
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros w hw z hz heq
    simp at heq
    have hw₂ := REquiv.translation_id hv hu hw
    have hz₂ := REquiv.translation_id hv hu hz
    rw [← hw₂, ← hz₂, heq]

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is surjective
from the 𝓛-class of `x` to that of `y`. -/
lemma REquiv.surjOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where y = x
    intros z hz
    use z
    rw [← WithOne.coe_inj] at hv ⊢
    simp_all
    obtain
    ⟨a, ha⟩ := hz.le
    rw [← ha, mul_assoc, hv]
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros z hz
    simp at hz ⊢
    use z * u
    constructor
    · rw [← hu]
      apply LEquiv.rmult_compat hz
    · apply REquiv.translation_id hu hv hz

/-- If `x * v = y` and `y * u = x`, then the map `w ↦ w * u` is the inverse of
`w ↦ w * v` when restricted to the 𝓛-classes of `x` and `y` -/
theorem REquiv.invOn_lClass (hv : x * v = y) (hu : y * u = x) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  simp [Set.InvOn, Set.LeftInvOn]
  constructor
  · intro z hz
    apply REquiv.translation_id hv hu hz
  · intro z hz
    apply REquiv.translation_id hu hv hz

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is a bijection from
the 𝓛-class of `x` to that of `y`. -/
theorem REquiv.bijOn_lClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · apply RPreorder.mapsTo_lClass hv
  · apply hr.injOn_lClass hv
  · apply hr.surjOn_lClass hv

theorem REquiv.exists_bij_on_lClass (hr : x 𝓡 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓛 ⟦y⟧𝓛 := by
  rcases hr.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp at hv; subst hv -- trivial case where `x = y`
    use id
    apply Set.bijOn_id
  | coe v =>
    simp [← WithOne.coe_mul] at hv
    use fun w ↦ w * v
    apply REquiv.bijOn_lClass hr hv

/-- If `x 𝓡 y` such that `x * v = y`,
then the map `w ↦ w * v` preserves 𝓗-classes. -/
lemma REquiv.bijOn_lClass_pres_hClass (hr : x 𝓡 y) (hv : x * v = y) {a b : S} (hw : a 𝓛 x)
  (hz : b 𝓛 x) : a 𝓗 b ↔ (fun w ↦ w * v) a 𝓗 (fun w ↦ w * v) b := by
  simp [HEquiv.iff_rEquiv_and_lEquiv]
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where `x = y`
    obtain ⟨z₁, hz₁⟩ := hw.le
    have hyv : ↑y * ↑v = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    have hr₃ : a * v 𝓡 a := by
      simp [REquiv]
      use 1
      simp [← hz₁, mul_assoc, hyv]
    obtain ⟨z₂, hz₂⟩ := hz.le
    have hr₄ : b 𝓡 b * v := by
      simp [REquiv]
      use 1
      simp [← hz₂, mul_assoc, hyv]
    constructor
    · rintro ⟨hr₂, hl⟩
      constructor
      · refine REquiv.trans hr₃ ?_
        apply REquiv.trans hr₂ hr₄
      · apply LEquiv.rmult_compat hl
    · rintro ⟨hr₁, hl⟩
      constructor
      · refine REquiv.trans hr₃.symm ?_
        apply REquiv.trans hr₁ hr₄.symm
      · apply LEquiv.trans hw hz.symm
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    have hid_a := REquiv.translation_id hv hu hw
    have hid_b := REquiv.translation_id hv hu hz
    have hr₂ : a * v 𝓡 a  := by
      simp [REquiv]
      use u
      simpa [← WithOne.coe_mul, WithOne.coe_inj]
    have hr₃ : b 𝓡 b * v := by
      simp [REquiv]
      use u
      simpa [← WithOne.coe_mul, WithOne.coe_inj]
    constructor
    · rintro ⟨hr₁, hl⟩
      constructor
      · refine REquiv.trans hr₂ ?_
        apply REquiv.trans hr₁ hr₃
      · apply LEquiv.rmult_compat hl
    · rintro ⟨hr₁, hl⟩
      constructor
      · refine REquiv.trans hr₂.symm ?_
        apply REquiv.trans hr₁ hr₃.symm
      · apply LEquiv.trans hw hz.symm

lemma REquiv.mapsTo_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.MapsTo (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where `x = y`
    intros z
    simp_all [HEquiv.iff_rEquiv_and_lEquiv]
    intros hrz hlz
    have hyv : ↑y * ↑v = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    have hr : z * v 𝓡 z := by
      obtain ⟨a, ha⟩ := hlz.le
      simp [REquiv]
      use 1
      simp [← ha, mul_assoc, hyv]
    constructor
    · apply REquiv.trans hr hrz
    · rw [← hv]
      apply LEquiv.rmult_compat hlz
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros z hz
    have hbij := hr.bijOn_lClass hv
    have h := hbij.mapsTo hz.to_lEquiv
    simp [HEquiv.iff_rEquiv_and_lEquiv]
    constructor
    · have hr₂ : z * v 𝓡 z := by
        simp [REquiv]
        use u
        simp [← WithOne.coe_mul]
        apply REquiv.translation_id hv hu
        exact hz.to_lEquiv
      refine REquiv.trans hr₂ ?_
      apply REquiv.trans hz.to_rEquiv hr
    · exact h

lemma REquiv.surjOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.SurjOn (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  have hsurj := hr.surjOn_lClass hv
  rcases hr.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where `x = y`
    intros z hz
    simp at hz ⊢
    specialize hsurj hz.to_lEquiv
    simp at hsurj
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    use w
    refine ⟨?_, hw₂⟩
    simp [HEquiv.iff_rEquiv_and_lEquiv]
    refine ⟨?_, hw₁⟩
    have hw₃ : w 𝓡 z := by
      simp [REquiv]
      constructor
      · use 1; simp only [mul_one]
        obtain ⟨u, hu⟩ := hw₁.le
        have hv' : ↑y * ↑v = (↑y : WithOne S) := by
          simp [← WithOne.coe_mul, hv]
        simp [← hw₂]
        rw [← hu, mul_assoc, hv']
      · use v; simp [hw₂.symm]
    apply REquiv.trans hw₃ hz.to_rEquiv
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros z hz
    specialize hsurj hz.to_lEquiv
    simp_all
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    use w
    simp_all [HEquiv.iff_rEquiv_and_lEquiv]
    have hw₃ : w 𝓡 z := by
      subst hw₂
      simp [REquiv]
      use u
      simp [← WithOne.coe_mul]
      exact REquiv.translation_id hv hu hw₁
    refine REquiv.trans hw₃ ?_
    apply REquiv.trans hz.1 hr.symm

lemma REquiv.injOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.InjOn (fun w ↦ w * v) ⟦x⟧𝓗 := by
  have h_inj := hr.injOn_lClass hv
  obtain ⟨u, hu⟩ := hr.le
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where `x = y`
    intros a ha b hb heq
    simp at ha hb heq ⊢
    refine h_inj ?_ ?_ ?_
    · exact ha.to_lEquiv
    · exact hb.to_lEquiv
    · simp_all
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros a ha b hb heq
    refine h_inj ?_ ?_ ?_
    · exact ha.to_lEquiv
    · exact hb.to_lEquiv
    · simp_all

lemma REquiv.invOn_hClass (hv : x * v = y) (hu : y * u = x) :
    Set.InvOn (fun w ↦ w * u) (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  simp [Set.InvOn, Set.LeftInvOn]
  constructor
  · intro z hz
    apply REquiv.translation_id hv hu hz.to_lEquiv
  · intro z hz
    apply REquiv.translation_id hu hv hz.to_lEquiv

/-- If `x 𝓡 y` such that `x * v = y`, then the map `w ↦ w * v` is a bijection from
the 𝓗-class of `x` to that of `y`. -/
theorem REquiv.bijOn_hClass (hr : x 𝓡 y) (hv : x * v = y) :
    Set.BijOn (fun w ↦ w * v) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · apply hr.mapsTo_hClass hv
  · apply hr.injOn_hClass hv
  · apply hr.surjOn_hClass hv

theorem REquiv.exists_bij_on_hClass (hr : x 𝓡 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hr.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp at hv; subst hv -- trivial case where `x = y`
    use id
    apply Set.bijOn_id
  | coe v =>
    simp [← WithOne.coe_mul] at hv
    use fun w ↦ w * v
    apply REquiv.bijOn_hClass hr hv


/-! ### Dual proofs -/

/-- If `x 𝓛 y` such that `u * y = x` and `v * x = y`, then left translation by `u * v` on any
element 𝓡-equivalent to `x` is the identity. -/
lemma LEquiv.translation_id (hv : v * x = y) (hu : u * y = x) (hw : w 𝓡 x) : u * v * w = w := by
  rcases hw.le with ⟨z, hz⟩
  cases z with
  | one => simp at hz; subst hz; rw [mul_assoc, hv, hu]
  | coe z =>
    simp [← WithOne.coe_mul] at hz
    subst hz
    rw [← mul_assoc, mul_assoc u, hv, hu]

/-- If `v * x = y`, then the map `w ↦ v * w`
maps the 𝓡-class of `x` to that of `y` -/
lemma LPreorder.mapsTo_rClass (hy : v * x = y) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp [Set.MapsTo]
  intros z hz
  rw [← hy]
  apply REquiv.lmult_compat
  exact hz

/-- If `x 𝓛 y` such that `v * x = y` then the map `w ↦ v * w` is injective on the
𝓡-class of `x`. -/
lemma LEquiv.injOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓡 := by
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one => -- trivial case, x = y
    simp at hu; subst hu
    intros w hw z hz heq
    simp at hw hz heq
    rw [← WithOne.coe_inj] at heq ⊢ hv
    simp at heq hv
    obtain ⟨a, ha⟩ := hw.le
    obtain ⟨b, hb⟩ := hz.le
    rwa [← ha, ← hb, ← mul_assoc, ← mul_assoc, hv, ha, hb] at heq
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros w hw z hz heq
    simp at heq
    have hw₂ := LEquiv.translation_id hv hu hw
    have hz₂ := LEquiv.translation_id hv hu hz
    rw [← hw₂, ← hz₂, mul_assoc, heq, ← mul_assoc]

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is surjective
from the 𝓡-class of `x` to that of `y`. -/
lemma LEquiv.surjOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where y = x
    intros z hz
    use z
    rw [← WithOne.coe_inj] at hv ⊢
    simp_all
    obtain ⟨a, ha⟩ := hz.le
    rw [← ha, ← mul_assoc, hv]
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros z hz
    simp at hz ⊢
    use u * z
    constructor
    · rw [← hu]
      apply REquiv.lmult_compat hz
    · rw [← mul_assoc]
      apply LEquiv.translation_id hu hv hz

/-- If `u * y = x` and `v * x = y`, then the map `w ↦ u * w` is the inverse of
`w ↦ v * w` when restricted to the 𝓡-classes of `x` and `y` -/
theorem LEquiv.invOn_rClass (hv : v * x = y) (hu : u * y = x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  simp [Set.InvOn, Set.LeftInvOn]
  constructor
  · intro z hz
    rw [← mul_assoc]
    apply LEquiv.translation_id hv hu hz
  · intro z hz
    rw [← mul_assoc]
    apply LEquiv.translation_id hu hv hz

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is a bijection from
the 𝓡-class of `x` to that of `y`. -/
theorem LEquiv.bijOn_rClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · apply LPreorder.mapsTo_rClass hv
  · apply hl.injOn_rClass hv
  · apply hl.surjOn_rClass hv

theorem LEquiv.exists_bijOn_rClass (hl : x 𝓛 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓡 ⟦y⟧𝓡 := by
  rcases hl.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp at hv; subst hv -- trivial case where `x = y`
    use id
    apply Set.bijOn_id
  | coe v =>
    simp [← WithOne.coe_mul] at hv
    use fun w ↦ v * w
    apply hl.bijOn_rClass hv

lemma LEquiv.mapsTo_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.MapsTo (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where `x = y`
    intros z
    simp_all [HEquiv.iff_rEquiv_and_lEquiv]
    intros hrz hlz
    have hvy : ↑v * ↑y = (↑y : WithOne S) := by
      simp [← WithOne.coe_mul, hv]
    have hl : v * z 𝓛 z := by
      obtain ⟨a, ha⟩ := hrz.le
      simp [LEquiv]
      use 1
      simp [← ha, ← mul_assoc, hvy]
    constructor
    · rw [← hv]
      apply REquiv.lmult_compat hrz
    · apply LEquiv.trans hl hlz
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros z hz
    have hbij := hl.bijOn_rClass hv
    have h := hbij.mapsTo hz.to_rEquiv
    simp [HEquiv.iff_rEquiv_and_lEquiv]
    constructor
    · exact h
    · have hl₂ : v * z 𝓛 z := by
        simp [LEquiv]
        use u
        simp [← WithOne.coe_mul, ← mul_assoc]
        apply LEquiv.translation_id hv hu
        exact hz.to_rEquiv
      refine LEquiv.trans hl₂ ?_
      apply LEquiv.trans hz.to_lEquiv hl

lemma LEquiv.surjOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.SurjOn (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  have hsurj := hl.surjOn_rClass hv
  rcases hl.le with ⟨u, hu⟩
  cases u with
  | one =>
    simp at hu; subst hu -- trivial case where `x = y`
    intros z hz
    simp at hz ⊢
    specialize hsurj hz.to_rEquiv
    simp at hsurj
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    use w
    refine ⟨?_, hw₂⟩
    simp [HEquiv.iff_rEquiv_and_lEquiv]
    refine ⟨hw₁, ?_⟩
    have hw₃ : w 𝓛 z := by
      simp [LEquiv]
      constructor
      · use 1; simp only [one_mul]
        obtain ⟨a, ha⟩ := hw₁.le
        have hy' : ↑v * ↑y = (↑y : WithOne S) := by
          simp [← WithOne.coe_mul, hv]
        simp [← hw₂]
        rw [← ha, ← mul_assoc, hy']
      · use v; simp [hw₂.symm]
    apply LEquiv.trans hw₃ hz.to_lEquiv
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    intros z hz
    specialize hsurj hz.to_rEquiv
    simp_all
    obtain ⟨w, hw₁, hw₂⟩ := hsurj
    use w
    simp_all [HEquiv.iff_rEquiv_and_lEquiv]
    have hw₃ : w 𝓛 z := by
      subst hw₂
      simp [LEquiv]
      use u
      simp [← WithOne.coe_mul, ← mul_assoc]
      exact LEquiv.translation_id hv hu hw₁
    refine LEquiv.trans hw₃ ?_
    apply LEquiv.trans hz.2 hl.symm

lemma LEquiv.injOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.InjOn (fun w ↦ v * w) ⟦x⟧𝓗 := by
  have h_inj := hl.injOn_rClass hv
  obtain ⟨u, hx⟩ := hl.ge
  cases u with
  | one =>
    simp at hx; subst hx -- trivial case where `x = y`
    intros a ha b hb heq
    simp at ha hb heq ⊢
    refine h_inj ?_ ?_ ?_
    · exact ha.to_rEquiv
    · exact hb.to_rEquiv
    · simp_all
  | coe u =>
    simp [← WithOne.coe_mul] at hx
    intros a ha b hb heq
    refine h_inj ?_ ?_ ?_
    · exact ha.to_rEquiv
    · exact hb.to_rEquiv
    · simp_all

lemma LEquiv.invOn_hClass (hv : v * x = y) (hu : u * y = x) :
    Set.InvOn (fun w ↦ u * w) (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  simp [Set.InvOn, Set.LeftInvOn]
  constructor
  · intro z hz
    rw [← mul_assoc]
    apply LEquiv.translation_id hv hu hz.to_rEquiv
  · intro z hz
    rw [← mul_assoc]
    apply LEquiv.translation_id hu hv hz.to_rEquiv

/-- If `x 𝓛 y` such that `v * x = y`, then the map `w ↦ v * w` is a bijection from
the 𝓗-class of `x` to that of `y`. -/
theorem LEquiv.bijOn_hClass (hl : x 𝓛 y) (hv : v * x = y) :
    Set.BijOn (fun w ↦ v * w) ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  refine Set.BijOn.mk ?_ ?_ ?_
  · apply hl.mapsTo_hClass hv
  · apply hl.injOn_hClass hv
  · apply hl.surjOn_hClass hv

theorem LEquiv.exists_bijOn_hClass (hl : x 𝓛 y) : ∃ f : S → S, Set.BijOn f ⟦x⟧𝓗 ⟦y⟧𝓗 := by
  rcases hl.ge with ⟨v, hv⟩
  cases v with
  | one =>
    simp at hv; subst hv -- trivial case where `x = y`
    use id
    apply Set.bijOn_id
  | coe v =>
    simp [← WithOne.coe_mul] at hv
    use fun w ↦ v * w
    apply hl.bijOn_hClass hv

end Semigroup
