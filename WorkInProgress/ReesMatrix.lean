import MyProject.Green.Location

/-! # Rees Matrix Semigroups -/

namespace Semigroup

section RegularSemigroup

variable {S : Type*} [Semigroup S]

def isRegularElem (x : S) : Prop :=
  ∃ y : S, x * y * x = x

def isRegularSemigroup : Prop :=
  ∀ x : S, isRegularElem x

end RegularSemigroup

universe u v w

section ReesWithoutZero

variable {I : Type u} {J : Type v} {G : Type w} [Group G] (P : I → J → G)

structure Rees (P : I → J → G) : Type (max v w u) where
  i : I
  j : J
  g : G

instance Rees.Mul : Mul (Rees P) where
  mul (a b : Rees P) := ⟨a.i, b.j, a.g * (P b.i a.j) * b.g⟩

@[simp] lemma Rees.mul_def (i₁ i₂ : I) (j₁ j₂ : J) (g₁ g₂ : G) :
    ⟨i₁, j₁, g₁⟩ * ⟨i₂, j₂, g₂⟩ = (⟨i₁, j₂, g₁ * (P i₂ j₁) * g₂⟩ : Rees P):= by
  rfl

instance Rees.Semigroup : Semigroup (Rees P) where
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
  rcases x
  · rfl
  · rfl

@[simp] lemma ReesZero.mul_def (x y : (ReesZero P)) :
    some x * some y =
      (match P y.i x.j with
        | some pg => (some ⟨x.i, y.j, x.g * pg * y.g⟩ : Option (ReesZero P))
        | none => (none : Option (ReesZero P))) := by
  rfl

lemma ReesZero.mul_of_ne_none (x y : ReesZero P) {g : G} (hp : P y.i x.j = some g) :
    some x * some y = some ⟨x.i, y.j, x.g * g * y.g⟩ := by
  simp_all [mul_def]

def ReesZero.semigroup : Semigroup (Option (ReesZero P)) where
  mul_assoc := by
    intro a b c
    rcases a with (hn | a)
    · simp
    rcases b with (hn | b)
    · simp
    rcases c with (hn | c)
    · simp
    simp
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

instance : Semigroup (Option (ReesZero P)) := ReesZero.semigroup P

/-- Given an element `(i, j, g)` of a *regular* Rees' Matrix semigroup with zero, there exists
a `i'` such that `P i' j ≠ none`. -/
lemma ReesZero.exists_nonzero_col (hreg : (ReesZero.semigroup P).isRegularSemigroup)
  (x : ReesZero P) :
    ∃ i' : I, P i' x.j ≠ none := by
  simp_all [isRegularSemigroup, isRegularElem]
  specialize hreg (some x)
  rcases hreg with ⟨y, hy⟩
  rcases y with (_ | y')
  · simp_all
  · simp_all
    by_cases hp : P y'.i x.j ≠ none
    · use y'.i
    · simp_all

/-- Given an element `(i, j, g)` of a *regular* Rees' Matrix semigroup with zero, there exists
a `j'` such that `P i j' ≠ none`. -/
lemma ReesZero.exists_nonzero_row (hreg : (ReesZero.semigroup P).isRegularSemigroup)
  (x : ReesZero P) :
    ∃ j' : J, P x.i j' ≠ none := by
  simp_all [isRegularSemigroup, isRegularElem]
  specialize hreg (some x)
  rcases hreg with ⟨y, hy⟩
  rcases y with (_ | y')
  · simp_all
  · simp_all
    by_cases hp : P y'.i x.j ≠ none
    · rw [Option.ne_none_iff_exists] at hp
      obtain ⟨g, hg⟩ := hp
      rw [← hg] at hy
      simp at hy
      by_cases hp₂ : P x.i y'.j ≠ none
      · exact ⟨y'.j, hp₂⟩
      · simp_all
    · simp_all

-- Does every row and every column have to be nonempty?
/-- A Rees Matrix semigroup with zero is Regular iff every row and every column of its
sandwich matrix has a nonzero entry. -/
theorem ReesZero.regular_iff_nonzero (hi : ∀ i, ∃ x : ReesZero P, x.i = i)
  (hj : ∀ j, ∃ x : ReesZero P, x.j = j) :
    (ReesZero.semigroup P).isRegularSemigroup ↔
    (∀ i : I, ∃ j : J, P i j ≠ none) ∧
    (∀ j : J, ∃ i : I, P i j ≠ none) := by
  constructor
  · intro hreg
    constructor
    · intro i
      obtain ⟨x, hx⟩ := hi i
      rw [← hx]
      exact ReesZero.exists_nonzero_row P hreg x
    · intro j
      obtain ⟨x, hx⟩ := hj j
      rw [← hx]
      exact ReesZero.exists_nonzero_col P hreg x
  · rintro ⟨hi₂, hj₂⟩
    simp [isRegularSemigroup, isRegularElem]
    intro x
    rcases x with (x | x)
    · use none
      simp
    · obtain ⟨j', hj'⟩ := hi₂ x.i
      obtain ⟨i', hi'⟩ := hj₂ x.j
      rw [Option.ne_none_iff_exists] at hi' hj'
      obtain ⟨y, hy⟩ := hi'
      obtain ⟨z, hz⟩ := hj'
      use some ⟨i', j', y⁻¹ * x.g⁻¹ * z⁻¹⟩
      simp [← hy, ← hz]
      congr
      simp [← mul_assoc]





end ReesWithZero

end Semigroup
