import MyProject.Green.GreensLemma
import MyProject.Green.Finite
import MyProject.Substructures
import Mathlib

/-!
# The Location Theorem

This file proves the Location Theorem, which states that the following
conditions are equivalent for `x y : S` where `S` is a semigroup:
  1. `x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
  2. `⟦x⟧𝓡 ∩ ⟦y⟧𝓛` contains an idempotent element.

If the semigroup is finite, these conditions are equivalent to
  3. `x * y 𝓓 x` (Alternatively, `x * y 𝓓 y`) and `x 𝓓 y`

Additionally, we prove that the 𝓗-class of an idempotent element is a group,
and we define this as a subgroup of the underlying semigroup.

## Main Definitions

* `HEquiv.subgroup_of_idempotent` - Given an idempotent element `e : S`, the 𝓗-class of `e`
as a subgroup of `S`

* `HEquiv.group_of_idempotent` - Given an idempotent element `e : S`, the H-class of `e`
as a group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}`

## Main Theorems

* `DEquiv.mul_in_inter_iff_equiv` - For `x y : S` where `S` is a finite semigroup, `x * y` is in
`⟦x⟧𝓡 ∩ ⟦y⟧𝓛` iff `x 𝓓 y 𝓓 x * y`. This proves the equivalence of statements 1 and 3 abolve.

* `mul_in_inter_iff_exists_idempotent` - For `x y : S`, `x * y` is in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`
iff there exists an idempotent element in `⟦x⟧𝓡 ∩ ⟦y⟧𝓛`. This proves the equivalence of statments
1 and 2 above.

## Refrences

TODO

## TODO/Notes

Should We prove the finite condition or just leave it talking about `J` equivalence?
-/

namespace Semigroup

variable {S : Type*} [Semigroup S] (x y : S)

/-- In Finite semigroups, `x * y` is in the intersection of the 𝓡-class of `x` and the 𝓛-class
of `y` iff `x`, `y`, and `x * y` are 𝓓-Equivalent. -/
theorem DEquiv.mul_in_inter_iff_equiv [Finite S] : x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ x 𝓓 y ∧ x * y 𝓓 x := by
  simp_all
  constructor
  · rintro ⟨hr, hl⟩
    constructor
    · use x * y
      exact ⟨hr.symm, hl⟩
    · exact JEquiv.to_dEquiv <| REquiv.to_jEquiv hr
  · rintro ⟨hj₁, hj₂⟩
    apply DEquiv.to_jEquiv at hj₁
    apply DEquiv.to_jEquiv at hj₂
    constructor
    · refine REquiv.of_rPreorder_and_jEquiv ?_ hj₂
      simp
    · refine LEquiv.of_lPreorder_and_jEquiv ?_ ?_
      · simp
      · apply JEquiv.trans hj₂ hj₁

/-- `x * y` is 𝓡-equivalent to `x` and 𝓛-equivalent to `y` iff there exists an idempotent
element in the intersection of the 𝓡-class of `y` and the 𝓛-class of `x`. -/
theorem mul_in_inter_iff_exists_idempotent :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
  constructor
  · simp_all [IsIdempotentElem]
    intro hr hl
    have heq : x * y = x * y := by rfl
    have hsurj := hr.symm.surjOn_lClass heq
    specialize hsurj hl.symm
    rcases hsurj with ⟨w, hw, hw_eq⟩
    simp at hw_eq hw
    use w
    refine ⟨?_, ⟨?_, hw⟩⟩
    · sorry
    · sorry
    have hid := REquiv.translation_id heq₂ heq₁ hw.symm
    simp at hw_eq
    nth_rw 2 [← hid]
    rw [hw_eq, ← mul_assoc, hid]
    simp
    constructor
    · constructor
      · use u
        simp [← WithOne.coe_mul]
        rw [← hw_eq, hid]
      · use y
        simp [← WithOne.coe_mul]
        rw [hw_eq]
    · exact hw


/- We would like to show that `w ↦ w * y` is a bijection from `⟦x]𝓛 to ⟦y⟧𝓛`, so that we can get
the pre-image of `y` as our idempotent. However we need the fact that there exists a `u` such that
`x = x * y * u`, so we need to destruct the witness of `x ≤𝓡 x * y` -/
    obtain ⟨u, hu⟩ := hr.2
    cases u with
    | one =>
      -- In this case, `x = x * y`, so `y` is idempotent
      use y
      simp_all
      have heq : x * y = x := by simpa [← WithOne.coe_mul] using hu
      have hl' := hl
      obtain ⟨_, ⟨a, ha⟩⟩ := hl'
      cases a with
      | one => -- trivial case where x = y
        simp at ha
        have heq' : x * y  = y := by simpa [← WithOne.coe_mul] using ha
        have heq'' : x = y := by rw [← heq]; nth_rw 2 [← heq']
        subst heq''
        simp [heq']
      | coe a =>
        rw [← heq] at hr
        simp [← mul_assoc] at ha
        have heq' : a * x * y = y := by simpa [← WithOne.coe_mul] using ha
        have hy : y * y = y := by
          nth_rw 1 [← heq', mul_assoc a, ← heq, ← heq']
        refine ⟨hy, ?_⟩
        rw [← heq]
        exact hl.symm
    | coe u =>
      have heq₁ : x * y = x * y := by rfl
      have heq₂ : x * y * u = x := by
        rw [← WithOne.coe_inj, WithOne.coe_mul]
        exact hu
      have hsurj := hr.surjOn_lClass heq₂
      have hu' : y ∈ ⟦x * y⟧𝓛 := by
        simp; exact hl.symm
      specialize hsurj hu'
      rcases hsurj with ⟨w, hw, hw_eq⟩
      use w
      have hid := REquiv.translation_id heq₂ heq₁ hw.symm
      simp at hw_eq
      nth_rw 2 [← hid]
      rw [hw_eq, ← mul_assoc, hid]
      simp
      constructor
      · constructor
        · use u
          simp [← WithOne.coe_mul]
          rw [← hw_eq, hid]
        · use y
          simp [← WithOne.coe_mul]
          rw [hw_eq]
      · exact hw
  · simp_all
    intro e hi hr hl
    have he₁ : y = e * y := by
      have hr₁ : y ≤𝓡 e := hr.2
      have he := RPreorder.le_idempotent y hi
      rwa [he] at hr₁
    have he₂ : x = x * e := by
      have hl₁ : x ≤𝓛 e := hl.2
      have he := LPreorder.le_idempotent x hi
      rwa [he] at hl₁
    constructor
    · nth_rw 2 [he₂]
      apply REquiv.lmult_compat y e x hr.symm
    · nth_rw 2 [he₁]
      apply LEquiv.rmult_compat x e y hl.symm

/-- Idempotent-containing 𝓗-classes are closed under multiplication. -/
lemma HEquiv.mul_closed_of_idempotent {e x y : S} (he : IsIdempotentElem e)
    (hx : x ∈ ⟦e⟧𝓗) (hy : y ∈ ⟦e⟧𝓗) : x * y ∈ ⟦e⟧𝓗 := by
  simp_all
  have he : ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
    use e
    simp_all [HEquiv.iff_rEquiv_and_lEquiv]
  rw [← mul_in_inter_iff_exists_idempotent x y] at he
  simp_all [HEquiv.iff_rEquiv_and_lEquiv]
  constructor
  · apply REquiv.trans he.1 hx.1
  · apply LEquiv.trans he.2 hy.2

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
left identity. -/
lemma HEquiv.idempotent_mul {e : S} (he : IsIdempotentElem e) {x : S} (hx : x ∈ ⟦e⟧𝓗) :
    e * x = x := by
  simp at hx
  rw [← RPreorder.le_idempotent he]
  apply REquiv.le
  simp [hx]

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
right identity. -/
lemma HEquiv.mul_idempotent {e : S} (he : IsIdempotentElem e) {x : S} (hx : x ∈ ⟦e⟧𝓗) :
    x * e = x := by
  simp at hx
  rw [← LPreorder.le_idempotent he]
  apply LEquiv.le
  simp [hx]

/-- All idempotent elements in an 𝓗 class are equal. -/
lemma HEquiv.idempotent_eq {e x : S} (hh : x 𝓗 e)
    (he : IsIdempotentElem e) (hx : IsIdempotentElem x) : e = x := by
  have hle := hh.le.1
  have hge := hh.ge.2
  rw [RPreorder.le_idempotent he] at hle
  rw [LPreorder.le_idempotent hx] at hge
  nth_rw 1 [← hle, ← hge]

-- TODO. use REquiv.bijOn_hClass below
/-- The 𝓗-class of an idempotent element is closed under inverses. -/
lemma HEquiv.exists_inverse_of_idempotent {e x : S} (he : IsIdempotentElem e) (hh : x ∈ ⟦e⟧𝓗) :
    ∃ y, y 𝓗 e ∧ x * y = e ∧ y * x = e := by
  simp at hh
  have hr₁ : e ≤𝓡 x := by simp [hh]
  obtain ⟨y, hy⟩ := hr₁
  cases y with
  | one =>
    simp at hy
    subst hy
    use x
    simp_all [IsIdempotentElem]
  | coe y =>
    have heq : x * y = e := by simpa [← WithOne.coe_mul] using hy
    have hex : e * x = x := HEquiv.idempotent_mul he hh
    have hxe : x * e = x := HEquiv.mul_idempotent he hh
    -- z ↦ z * x is a bijection on the HClass of e
    have hsurj := hh.symm.to_rEquiv.surjOn_lClass hex
    have hein : e ∈ ⟦x⟧𝓛 := by simp_all
    specialize hsurj hein
    rcases hsurj with ⟨z, hz, hz_eq⟩
    simp_all
    have hez : z 𝓗 e := by
      have hl : e 𝓛 e := by simp
      have hpres := hh.symm.to_rEquiv.bijOn_lClass_pres_hClass hex hz hl
      rw [hpres]
      simp [hz_eq, hex]
      exact hh.symm
    use z
    refine ⟨hez, ?_, ?_⟩
    · have hl₁ : e 𝓛 e := by simp
      have hl₂ : x * z 𝓛 e := by
        apply HEquiv.to_lEquiv
        apply HEquiv.mul_closed_of_idempotent he hh hez
      have hinj := hh.symm.to_rEquiv.injOn_lClass hex
      specialize hinj hl₂ hl₁
      simp at hinj
      apply hinj
      rw [mul_assoc, hz_eq, hex, hxe]
    · exact hz_eq

/-- The 𝓗-class of an idempotent element as a subgroup of the semigroup. -/
noncomputable def HEquiv.subgroup_of_idempotent {e : S} (he : IsIdempotentElem e) : Subgroup S where
  carrier := ⟦e⟧𝓗
  mul_mem := HEquiv.mul_closed_of_idempotent he
  one := e
  one_mem := by simp
  one_mul {x : S} (hx : x 𝓗 e) := HEquiv.idempotent_mul he hx
  mul_one {x : S} (hx : x 𝓗 e) := HEquiv.mul_idempotent he hx
  inv (x : S) := by
    have hd : Decidable (x ∈ ⟦e⟧𝓗) := by exact Classical.propDecidable (x ∈ ⟦e⟧𝓗)
    exact (if hx : x ∈ ⟦e⟧𝓗
      then Exists.choose (HEquiv.exists_inverse_of_idempotent he hx)
      else x )
  inv_not_mem := by simp_all
  inv_mem := by
    simp_all
    intros x hx
    have h := Classical.choose_spec (HEquiv.exists_inverse_of_idempotent he hx)
    exact h.1
  inv_mul := by
    simp_all
    intros x hx
    have h := Classical.choose_spec (HEquiv.exists_inverse_of_idempotent he hx)
    exact h.2.2
  mul_inv := by
    simp_all
    intros x hx
    have h := Classical.choose_spec (HEquiv.exists_inverse_of_idempotent he hx)
    exact h.2.1

@[simp] lemma HEquiv.subgroup_of_idempotent_carrier_def {e : S} (he : IsIdempotentElem e) :
    (HEquiv.subgroup_of_idempotent he).carrier = ⟦e⟧𝓗 := by
  rfl

/-- The 𝓗-class of a semigroup as a Group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}` -/
noncomputable instance HEquiv.group_of_idempotent {e : S} (he : IsIdempotentElem e) :
    Group (HEquiv.subgroup_of_idempotent he) := by
  infer_instance

/-- The 𝓗-class of a semigroup as a Group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}` -/
noncomputable instance HEquiv.group_of_idempotent' {e : S} (he : IsIdempotentElem e) :
    Group ({x // x ∈ ⟦e⟧𝓗}) := by
  have h:= HEquiv.group_of_idempotent he
  exact h

/-- If there exists an `x, y` in an 𝓗 class such that `x * y` remains in the 𝓗-class,
then that 𝓗 class contains an idempotent. -/
theorem HEquiv.idempotent_in_subgroup {x y : S} (h₁ : x 𝓗 y) (h₂ : x * y 𝓗 x) :
    ∃ e, e 𝓗 x ∧ IsIdempotentElem e := by
  have hh : x * y 𝓗 y := by apply HEquiv.trans h₂ h₁
  have h := mul_in_inter_iff_exists_idempotent x y
  simp_all
  obtain ⟨e, he₁, he₂⟩ := h
  use e
  constructor
  · simp_all [HEquiv.iff_rEquiv_and_lEquiv]
    apply REquiv.trans he₂.1 h₁.1.symm
  · exact he₁

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓡-class. -/
theorem DEquiv.idempotent_in_rClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
    ∃ f ∈ ⟦x⟧𝓡, IsIdempotentElem f := by
  obtain ⟨r, hr₁, hr₂⟩ := hx
  have her : r * e = r := by
    have h := LPreorder.le_idempotent he r
    rw [← h]
    exact hr₂.le
  obtain ⟨u, hu⟩ := hr₂.ge
  cases u with
  | one =>
    use r
    simp_all
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    use r * u
    constructor
    · simp
      refine REquiv.trans ?_ hr₁.symm
      constructor
      · use u; simp
      · use r
        simp [← WithOne.coe_mul, mul_assoc, hu, her]
    · simp [IsIdempotentElem, ← mul_assoc]
      rw [mul_assoc r, hu, her]

/-- If a 𝓓-class contains an idempotent, it contains at least one idempotent
in each 𝓛-class. -/
theorem DEquiv.idempotent_in_lClass {e x : S} (he : IsIdempotentElem e) (hx : x 𝓓 e) :
    ∃ f ∈ ⟦x⟧𝓛, IsIdempotentElem f := by
  obtain ⟨r, hr₁, hr₂⟩ := hx.symm
  have her : e * r = r := by
    have h := RPreorder.le_idempotent he r
    rw [← h]
    exact hr₁.ge
  obtain ⟨u, hu⟩ := hr₁.le
  cases u with
  | one =>
    simp_all; subst hu
    use r
  | coe u =>
    simp [← WithOne.coe_mul] at hu
    use u * r
    constructor
    · simp
      refine LEquiv.trans ?_ hr₂
      constructor
      · use u; simp
      · use r
        simp [← WithOne.coe_mul, ← mul_assoc, hu, her]
    · simp [IsIdempotentElem, ← mul_assoc]
      rw [mul_assoc u, hu, mul_assoc, her]

lemma HEquiv.ofSubgroup {x y : S} {H : Subgroup S} (hx : x ∈ H) (hy : y ∈ H) : x 𝓗 y := by
  simp_all [HEquiv.iff_rEquiv_and_lEquiv, REquiv, LEquiv]
  constructor
  · constructor
    · use (H.inv y * x)
      simp [← WithOne.coe_mul, ← mul_assoc, H.mul_inv hy, H.one_mul x hx]
    · use (H.inv x * y)
      simp [← WithOne.coe_mul, ← mul_assoc, H.mul_inv hx, H.one_mul y hy]
  · constructor
    · use (x * H.inv y)
      simp [← WithOne.coe_mul, mul_assoc, H.inv_mul hy, H.mul_one x hx]
    · use (y * H.inv x)
      simp [← WithOne.coe_mul, mul_assoc, H.inv_mul hx, H.mul_one y hy]

/-- A maximal subgroup is the 𝓗-class of an idempotent. -/
theorem HEquiv.hClass_of_subgroup {H : Subgroup S} (hH : H.isMaximal) :
    ∃ e : S, IsIdempotentElem e ∧ H.carrier = ⟦e⟧𝓗 := by
  use H.one
  have hidem : IsIdempotentElem H.one := by
    simp [IsIdempotentElem]
    apply H.one_mul
    exact H.one_mem
  let K := HEquiv.subgroup_of_idempotent hidem
  have hle : H ≤ K := by
    intros x hx
    rw [K.mem_def]
    simp [K, subgroup_of_idempotent]
    apply HEquiv.ofSubgroup hx H.one_mem
  constructor
  · exact hidem
  · specialize hH K hle
    rw [hH]
    simp [subgroup_of_idempotent, K]

/-- Let `e f : S` be idempotent elements.
Let `e 𝓓 f` such that we have a `s` with `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
Then, the map `x ↦ t * x * s` is a bijection from the 𝓗-class of `e` to the 𝓗-class of `f`. -/
lemma DEquiv.bij_on_hClass {e f s t : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
  (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    Set.BijOn (fun x ↦ t * x * s) ⟦e⟧𝓗 ⟦f⟧𝓗 := by
  have hes : e * s = s := by
    rw [← RPreorder.le_idempotent he]
    exact hr.ge
  have hsf : s * f = s := by
    rw [← LPreorder.le_idempotent hf]
    exact hl.le
  -- `x ↦ x * s` is a bijection from ⟦e⟧𝓗 to ⟦s⟧𝓗
  obtain ⟨hs_map, hs_inj, hs_surj⟩ := hr.bijOn_hClass hes
  -- `x ↦ t * x` is a bijection from ⟦s⟧𝓗 to ⟦f⟧𝓗
  obtain ⟨ht_map, ht_inj, ht_surj⟩ := hl.bijOn_hClass ht
  refine Set.BijOn.mk ?_ ?_ ?_
  · intros x hx
    simp
    have hh : x * s 𝓗 s := by
      specialize hs_map hx
      simp_all
    specialize ht_map hh
    simpa [← mul_assoc] using ht_map
  · intros x hs y hy heq
    simp [mul_assoc] at heq
    have heq : x * s = y * s := by exact ht_inj (hs_map hs) (hs_map hy) heq
    refine hs_inj hs hy heq
  · intros y hy
    specialize ht_surj hy
    simp at ht_surj
    rcases ht_surj with ⟨z, hz, hz_eq⟩
    specialize hs_surj hz
    rcases hs_surj with ⟨w, hw, hw_eq⟩
    use w
    refine ⟨hw, ?_⟩
    simp_all
    simp [mul_assoc]
    rw [hw_eq, hz_eq]

/-- Let `e f : S` be idempotent elements.
Let `e 𝓓 f` such that we have a `s` with `e 𝓡 s` and `s 𝓛 f`.
Let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
let `u` be the witness of `e ≤𝓡 s` such that `s * u = e`.
Then, the map `x ↦ t * x * s` is a bijection which preserves multiplication (like a morphism). -/

lemma DEquiv.bij_on_hClass_map_mul {e f s t x y : S} (_ : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f)
  (_ : x 𝓗 e) (hy : y 𝓗 e) :
    (fun x ↦ t * x * s) x * (fun x ↦ t * x * s) y = (fun x ↦ t * x * s) (x * y) := by
  simp
  have hsf : s * f = s := by
    rw [← LPreorder.le_idempotent hf]
    exact hl.le
  have hidem : IsIdempotentElem (s * t) := by
    simp [IsIdempotentElem]
    rw [← mul_assoc, mul_assoc s, ht, hsf]
  have hsty : s * t * y = y := by
    rw [← RPreorder.le_idempotent hidem]
    apply REquiv.le
    have hr₂ : s 𝓡 s * t := by
      simp [REquiv]
      use s
      simp [← WithOne.coe_mul, mul_assoc, ht, hsf]
    refine REquiv.trans hy.to_rEquiv ?_
    apply REquiv.trans hr hr₂
  nth_rw 2 [← hsty]
  simp [← mul_assoc]

noncomputable def DEquiv.hClass_equiv {e f s t : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hr : e 𝓡 s) (hl : s 𝓛 f) (ht : t * s = f) :
    HEquiv.subgroup_of_idempotent he ≃* HEquiv.subgroup_of_idempotent hf := by
  refine Subgroup.hom_of_bijOn
    (HEquiv.subgroup_of_idempotent he)
    (HEquiv.subgroup_of_idempotent hf)
    (fun x ↦ t * x * s)
    (DEquiv.bij_on_hClass he hf hr hl ht) ?_
  · intros w z hw hz
    symm
    exact DEquiv.bij_on_hClass_map_mul he hf hr hl ht hw hz

lemma DEquiv.hClass_equiv' {e f : S} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) (hd : e 𝓓 f) :
    Nonempty (HEquiv.subgroup_of_idempotent he ≃* HEquiv.subgroup_of_idempotent hf) := by
  obtain ⟨s, hr, hl⟩ := hd
  -- let `t` be the witness of `f ≤𝓛 s` such that `t * s = f`.
  obtain ⟨t, ht⟩ := hl.ge
  cases t with
  | one =>
    simp at ht; subst ht -- trivial case where `f = s`
    /-
    obtain ⟨f, hbij⟩ := hr.exists_bij_on_hClass
    apply Nonempty.intro
    refine Subgroup.hom_of_bijOn
      (HEquiv.subgroup_of_idempotent he) -- `⟦e⟧𝓗`
      (HEquiv.subgroup_of_idempotent hf) -- `⟦f⟧𝓗`
      f ?_ ?_
      -/


    -- let `u` be the witness of `f ≤𝓡 e` such that `e * u = f`
    obtain ⟨u, hu⟩ := hr.ge
    cases u with
    | one => -- trivial case where `e = f`
      simp_all
      have heq : HEquiv.subgroup_of_idempotent he = HEquiv.subgroup_of_idempotent hf := by
        congr
      rw [heq]
      apply Nonempty.intro
      rfl
    | coe u =>
      simp [← WithOne.coe_mul] at hu
      -- ` f = e * u` and `e 𝓡 f`
      apply Nonempty.intro
      refine Subgroup.hom_of_bijOn
        (HEquiv.subgroup_of_idempotent he) -- `⟦e⟧𝓗`
        (HEquiv.subgroup_of_idempotent hf) -- `⟦f⟧𝓗`
        (fun x ↦ x * u) ?_ ?_
      · simp
        apply hr.bijOn_hClass hu
      · intros x y hx hy
        simp
        sorry --was this the correct bijection? is this provable?
  | coe t =>
    simp [← WithOne.coe_mul] at ht
    apply Nonempty.intro
    refine Subgroup.hom_of_bijOn
      (HEquiv.subgroup_of_idempotent he) -- `⟦e⟧𝓗`
      (HEquiv.subgroup_of_idempotent hf) -- `⟦f⟧𝓗`
      (fun x ↦ t * x * s) ?_ ?_
    · -- Lemmas Handle non-trivial case
      exact DEquiv.bij_on_hClass he hf hr hl ht
    · intros x y hx hy
      symm; exact DEquiv.bij_on_hClass_map_mul he hf hr hl ht hx hy

/-- Two maximal subgroups of a 𝓓-class are isomorphic. -/
def DEquiv.maximal_subgroups_equiv {x y : S} {H K : Subgroup S}
  (hH : H.isMaximal) (hK : K.isMaximal) (hx : x ∈ H) (hy : x ∈ K) (hd : x 𝓓 y) : Nonempty (H ≃* K) := by
  sorry

end Semigroup
