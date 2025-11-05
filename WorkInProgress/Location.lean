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

theorem mul_in_inter_iff_exists_idempotent :
    x * y ∈ ⟦x⟧𝓡 ∩ ⟦y⟧𝓛 ↔ ∃ e, IsIdempotentElem e ∧ e ∈ ⟦y⟧𝓡 ∩ ⟦x⟧𝓛 := by
  constructor
  · simp_all [IsIdempotentElem]
    intro hr hl
    -- We would like to show that `w ↦ w * y` is a bijection from `⟦x]𝓛 to ⟦y⟧𝓛`
    -- however we need the fact that there exists a `u` such that `x = x * y * u`,
    -- so we need to desctruct the witness of `x ≤𝓡 x * y`
    obtain ⟨u, hu⟩ := hr.2
    cases u with
    | one =>
      -- In this case, `x = x * y`, so `y` is idempotent?
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
      have he := RPreorder.le_idempotent y e hi
      rwa [he] at hr₁
    have he₂ : x = x * e := by
      have hl₁ : x ≤𝓛 e := hl.2
      have he := LPreorder.le_idempotent x e hi
      rwa [he] at hl₁
    constructor
    · nth_rw 2 [he₂]
      apply REquiv.lmult_compat y e x hr.symm
    · nth_rw 2 [he₁]
      apply LEquiv.rmult_compat x e y hl.symm

def HEquiv.subgroup_of_idempotent (e : S) (he : IsIdempotentElem e) : Subgroup S where
  carrier := ⟦e⟧𝓗
  mul_mem := sorry
  one := e
  one_mem := by simp
  one_mul := by sorry
  mul_one := by sorry
  inv := sorry
  inv_not_mem := sorry
  inv_mem := sorry
  inv_mul := sorry
  mul_inv := sorry

instance HEquiv.group_of_idempotent (e : S) (he : IsIdempotentElem e) :
    Group (HEquiv.subgroup_of_idempotent e he) := by
  infer_instance

end Semigroup
