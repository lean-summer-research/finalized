import MyProject.Green.Location

/-! # Rees Matrix Semigroups -/

namespace Semigroup

universe u v w

section ReesWithoutZero

variable {I : Type u} {J : Type v} {G : Type w} [Group G]

structure Rees (P : I → J → G) : Type (max v w u) where
  i : I
  j : J
  g : G

instance Rees.Mul (P : I → J → G) : Mul (Rees P) where
  mul (a b : Rees P) := ⟨a.i, b.j, a.g * (P b.i a.j) * b.g⟩

@[simp] lemma Rees.mul_def (P : I → J → G) (i₁ i₂ : I) (j₁ j₂ : J) (g₁ g₂ : G) :
    ⟨i₁, j₁, g₁⟩ * ⟨i₂, j₂, g₂⟩ = (⟨i₁, j₂, g₁ * (P i₂ j₁) * g₂⟩ : Rees P):= by
  rfl

instance (P : I → J → G) : Semigroup (Rees P) where
  mul_assoc := by
    rintro ⟨i₁, j₁, g₁⟩ ⟨i₂, j₂, g₂⟩ ⟨i₃, j₃, g₃⟩
    simp [← mul_assoc]

end ReesWithoutZero

section ReesWithZero

variable {I : Type u} {J : Type v} {G : Type w} [Group G]

structure ReesZero (P : I → J → (WithZero G)) : Type (max v w u) where
  i : I
  j : J
  g : G

variable (P : I → J → (WithZero G))

instance ReesZero.Mul : Mul (Option (ReesZero P)) where
  mul (x y : Option (ReesZero P)) :=
    match x, y with
    | some a, some b =>
      let pg := P b.i a.j
      match pg with
      | some pg => some ⟨a.i, b.j, a.g * pg * b.g⟩
      | none => none
    | _, _ => none

@[simp] lemma ReesZero.none_mul (x : Option (ReesZero P)) :
    none * x = none := by
  rfl

@[simp] lemma ReesZero.mul_none (x : Option (ReesZero P)) :
    x * none = none := by
  rcases x with (hn | hs)
  · rfl
  · rfl

@[simp] lemma ReesZero.mul_def (x y : (ReesZero P)) :
    some x * some y =
      (match P y.i x.j with
        | some pg => (some ⟨x.i, y.j, x.g * pg * y.g⟩ : Option (ReesZero P))
        | none => (none : Option (ReesZero P))) := by
  rfl

instance : Semigroup (Option (ReesZero P)) where
  mul_assoc := by
    intro a b c
    rcases a with (hn | a)
    · simp
    rcases b with (hn | b)
    · simp
    rcases c with (hn | c)
    · simp
    simp
    let pg := P b.i a.j
    by_cases h₁ : P b.i a.j ≠ none
    · rw [Option.ne_none_iff_exists] at h₁
      obtain ⟨p₁, hp₁⟩ := h₁
      simp [← hp₁]
      · by_cases h₂ : P c.i b.j ≠ none
        · rw [Option.ne_none_iff_exists] at h₂
          obtain ⟨p₂, hp₂⟩ := h₂
          simp [← hp₂, ← hp₁, ← mul_assoc]
        · simp_all
    · simp_all
      by_cases h₁ : P c.i b.j ≠ none
      · rw [Option.ne_none_iff_exists] at h₁
        obtain ⟨p₁, hp₁⟩ := h₁
        simp [← hp₁, h₁]
      · simp_all

end ReesWithZero

end Semigroup
