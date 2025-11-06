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
/- We would like to show that `w ↦ w * y` is a bijection from `⟦x]𝓛 to ⟦y⟧𝓛`, so that we can get
the pre-image of `y` as our idempotent. However we need the fact that there exists a `u` such that
`x = x * y * u`, so we need to destruct the witness of `x ≤𝓡 x * y` -/
    obtain ⟨u, hu⟩ := hr.2
    cases u with
    | one =>
      -- In this case, `x = x * y`, so `y` is idempotent
      use y
      simp_all
      have heq : x = x * y := by simpa [← WithOne.coe_mul] using hu
      have hl' := hl
      obtain ⟨_, ⟨a, ha⟩⟩ := hl'
      cases a with
      | one => -- trivial case where x = y
        simp at ha
        have heq' : y = x * y := by simpa [← WithOne.coe_mul] using ha
        have heq'' : x = y := by rw [heq]; nth_rw 2 [heq']
        subst heq''
        simp [heq'.symm]
      | coe a =>
        rw [← heq] at hr
        simp [← mul_assoc] at ha
        have heq' : y = a * x * y:= by simpa [← WithOne.coe_mul] using ha
        have hy : y * y = y := by
          nth_rw 1 [heq', mul_assoc a, ← heq, ← heq']
        refine ⟨hy, ?_⟩
        rw [heq]
        exact hl.symm
    | coe u =>
      have heq₁ : x * y = x * y := by rfl
      have heq₂ : x = x * y * u := by
        rw [← WithOne.coe_inj, WithOne.coe_mul]
        exact hu
      have hsurj := REquiv.surj_on_lClass heq₂ heq₁
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

/-- The 𝓗-class of an idempotent element is closed under inverses. -/
lemma HEquiv.exists_inverse_of_idempotent {e x : S} (he : IsIdempotentElem e) (hh : x ∈ ⟦e⟧𝓗) :
    ∃ y, y 𝓗 e ∧ x * y = e ∧ y * x = e := by
  have h₁ : x * e = x := by sorry
  have h₂ : e * x = x := by sorry
  simp at hh
  have hr₁ : e ≤𝓡 x := by simp [hh]
  obtain ⟨y, hy⟩ := hr₁
  cases y with
  | one =>
    simp at hy
    subst hy
    use e
  | coe y =>
    have heq : e = x * y := by simpa [← WithOne.coe_mul] using hy
    have hSurj := REquiv.surj_on_lClass heq h₂.symm
    have he₂ : e ∈ ⟦x⟧𝓛 := by simp [hh]
    specialize hSurj he₂
    obtain ⟨z, ⟨hz₁, hz₂⟩⟩ := hSurj
    simp at hz₂
    use z
    have hInj := REquiv.inj_on_lClass heq h₂.symm
    have h₃ : x * z ∈ ⟦e⟧𝓛 := by
      simp
      have hpres := LEquiv.bij_on_rClass hz₂.symm h₁.symm
      sorry
    have h₄ : e ∈ ⟦e⟧𝓛 := by simp
    specialize hInj h₃ h₄
    simp at hInj
    rw [mul_assoc, hz₂, h₁, h₂] at hInj
    simp at hInj
    constructor
    · have hz₃ : e 𝓛 z := by symm; simp_all
      have hpres := REquiv.bij_on_lClass_pres_hClass heq h₂.symm hz₁.symm h₄
      rw [hpres]
      rw [hz₂, h₂]
      exact hh.symm
    · exact ⟨hInj, hz₂⟩

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
lemma HEquiv.idempotent_mul {e : S} (he : IsIdempotentElem e) (x : S) (hx : x ∈ ⟦e⟧𝓗) :
    e * x = x := by
  simp at hx
  symm
  rw [← RPreorder.le_idempotent x he]
  apply REquiv.le
  simp [hx]

/-- For all elements in the 𝓗-class of an idempotent, that idempotent acts as a
right identity. -/
lemma HEquiv.mul_idempotent {e : S} (he : IsIdempotentElem e) (x : S) (hx : x ∈ ⟦e⟧𝓗) :
    x * e = x := by
  simp at hx
  symm
  rw [← LPreorder.le_idempotent x he]
  apply LEquiv.le
  simp [hx]

/-- The 𝓗-class of an idempotent element as a subgroup of the semigroup. -/
noncomputable def HEquiv.subgroup_of_idempotent (e : S) (he : IsIdempotentElem e) : Subgroup S where
  carrier := ⟦e⟧𝓗
  mul_mem := HEquiv.mul_closed_of_idempotent he
  one := e
  one_mem := by simp
  one_mul := HEquiv.idempotent_mul he
  mul_one := HEquiv.mul_idempotent he
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

/-- The 𝓗-class of a semigroup as a Group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}` -/
noncomputable instance HEquiv.group_of_idempotent (e : S) (he : IsIdempotentElem e) :
    Group (HEquiv.subgroup_of_idempotent e he) := by
  infer_instance

/-- The 𝓗-class of a semigroup as a Group on the subtype `{x : S // x ∈ ⟦e⟧𝓗}` -/
noncomputable instance HEquiv.group_of_idempotent' (e : S) (he : IsIdempotentElem e) :
    Group ({x // x ∈ ⟦e⟧𝓗}) := by
  have h:= HEquiv.group_of_idempotent e he
  exact h

end Semigroup
