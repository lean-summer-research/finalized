import MyProject.Green.Defs
import MyProject.Substructures
import Mathlib

namespace Semigroup

section GreensRelations

variable {S : Type*} [Semigroup S] (T : Subsemigroup S) (s₁ s₂ : S)

def RPreorder.ofSubsemigroup : Prop :=
  ∃ (h₁ : s₁ ∈ T) (h₂ : s₂ ∈ T), @RPreorder ↑T _ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩

notation s₁ " ≤𝓡{" T "} " s₂ => RPreorder.ofSubsemigroup T s₁ s₂

def REquiv.ofSubsemigroup : Prop :=
  ∃ (h₁ : s₁ ∈ T) (h₂ : s₂ ∈ T), (⟨s₁, h₁⟩ : T) 𝓡 ⟨s₂, h₂⟩

notation s₁ " 𝓡{" T "} " s₂ => REquiv.ofSubsemigroup T s₁ s₂

#check SetLike.coe_eq_coe
#check Finset.card_eq_of_equiv_fin
#check Finset.subtype

lemma RPreorder.ofSubsemigroup_if {s₁ s₂ : S} {h₁ : s₁ ∈ T} {h₂ : s₂ ∈ T}
    (hr : (⟨s₁, h₁⟩ : T) ≤𝓡 ⟨s₂, h₂⟩) : s₁ ≤𝓡 s₂ := by
  obtain ⟨z, hz⟩ := hr
  cases z with
  | one =>
    simp_all
  | coe z =>
    use ↑↑z
    simp_all [← WithOne.coe_mul]

example {t₁ t₂ : ↑T} : t₁ 𝓡 t₂ := by sorry

example {t₁ t₂ : ↑T} : (t₁ : S) 𝓡 t₂ := by sorry

theorem REquiv.ofSubsemigroup_iff (h₁ : s₁ ∈ T) (h₂ : s₂ ∈ T) : (s₁ 𝓡{T} s₂) ↔ s₁ 𝓡 s₂ := by
  simp [REquiv.ofSubsemigroup]
  constructor
  · rintro ⟨h₁, h₂, ⟨hr₁, hr₂⟩⟩
    simp_all [REquiv]
    constructor
    · apply RPreorder.ofSubsemigroup_if T hr₁
    · apply RPreorder.ofSubsemigroup_if T hr₂
  · rintro ⟨⟨z, hz⟩, ⟨v, hv⟩⟩
    use h₁, h₂
    cases z with
    | one =>
      simp at hz; subst hz; simp
    | coe z =>
       simp [← WithOne.coe_mul] at hz
       cases v with
       | one =>
         simp at hv; subst hv; simp
       | coe v =>
         simp [← WithOne.coe_mul] at hv
         sorry

end GreensRelations

section DClass

/-!
prop 1.8:
All maximal subgroups within a D class are isomorphic

NOTE : I dont think this is possible as a `def`
-/

variable {S : Type*} [Semigroup S] {x y : S}

def DEquiv.maximalSubgroupsEquiv {G₁ G₂ : Subgroup S}
  (h₁ : x ∈ G₁) (h₂ : y ∈ G₂) (hd : x 𝓓 y) : ↑G₁ ≃* ↑G₂ where
  toFun := sorry
  invFun := sorry
  map_mul' := by sorry


#check GroupWithZero
#check WithZero

end DClass

end Semigroup
