import MyProject.Green.Defs
import MyProject.Substructures
import Mathlib

namespace Semigroup

section GreensRelations

variable {S : Type*} [Semigroup S] (T : Subsemigroup S) (s₁ s₂ : S)

def RPreorder.ofSubsemigroup : Prop :=
  ∃ (h₁ : s₁ ∈ T) (h₂ : s₂ ∈ T), @RPreorder ↑T _ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩

notation s₁ " ≤𝓡{" T "} " s₂ => RPreorder.ofSubsemigroup T s₁ s₂
theorem RPreorder.ofSubsemigroup_iff (h₁ : s₁ ∈ T) (h₂ : s₂ ∈ T) : (s₁ ≤𝓡{T} s₂) ↔ s₁ ≤𝓡 s₂ := by
  simp [RPreorder.ofSubsemigroup]
  constructor
  · rintro ⟨h₁, h₂, hr⟩
    obtain ⟨z, hz⟩ := hr
    cases z with
    | one =>
      simp at hz
      rw [hz]
      simp
    | coe z =>
      use ↑↑z
      simp_all [← WithOne.coe_mul]
  · intro h
    use h₁, h₂
    obtain ⟨z, hz⟩ := h
    cases z with
    | one =>
      simp at hz
      subst hz
      simp
    | coe z =>
      sorry

end GreensRelations

section DClass

/-!
All maximal subgroups within a D class are isomorphic
-/

variable {S : Type*} [Semigroup S] {x y : S}

def DEquiv.maximal_subgroups_isomorphism {G₁ G₂ : Subgroup S}
  (h₁ : x ∈ G₁) (h₂ : y ∈ G₂) (hd : x 𝓓 y) : ↑G₁ ≃* ↑G₂ := sorry


end DClass

end Semigroup
