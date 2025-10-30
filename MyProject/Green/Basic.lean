import Mathlib.Algebra.Group.Idempotent
import MyProject.Green.Defs

/-!
# Basic Properties of Green's Relations

This file proves basic properties about Green's relations and idempotent elements.

We also prove that Green's relations are preserved under morphisms.

## Main theorems

Characterizations of elements that are 𝓡-below, 𝓛-below, or 𝓗-below an idempotent:
* `Semigroup.RPreorder.le_idempotent` - `x ≤𝓡 e ↔ x = e * x`.
* `Semigroup.LPreorder.le_idempotent` - `x ≤𝓛 e ↔ x = x * e`.
* `Semigroup.HPreorder.le_idempotent` - `x ≤𝓗 e ↔ x = e * x ∧ x = x * e`.

Green's relations are preserved under semigroup morphisms `f`:
* `Semigroup.RPreorder.hom_pres` - `x ≤𝓡 y → f x ≤𝓡 f y`.
* `Semigroup.LPreorder.hom_pres` - `x ≤𝓛 y → f x ≤𝓛 f y`.
* `Semigroup.JPreorder.hom_pres` - `x ≤𝓙 y → f x ≤𝓙 f y`.
* `Semigroup.HPreorder.hom_pres` - `x ≤𝓗 y → f x ≤𝓗 f y`.
* `Semigroup.REquiv.hom_pres` - `x 𝓡 y → f x 𝓡 f y`.
* `Semigroup.LEquiv.hom_pres` - `x 𝓛 y → f x 𝓛 f y`.
* `Semigroup.JEquiv.hom_pres` - `x 𝓙 y → f x 𝓙 f y`.
* `Semigroup.HEquiv.hom_pres` - `x 𝓗 y → f x 𝓗 f y`.
* `Semigroup.DEquiv.hom_pres` - `x 𝓓 y → f x 𝓓 f y`.

## References

TODO

## Blueprint

* One entry for the characterization lemmas of elements below idempotents.
Label : le-idempotent
Tagged Lean lemmas :
 - `Semigroup.RPreorder.le_idempotent`
 - `Semigroup.LPreorder.le_idempotent`
 - `Semigroup.HPreorder.le_idempotent`
Content : prove it for R and H, say L holds by a similar argument to R
Dependencies : greens-relations

* One entry for the morphism preservation lemmas.
Label : greens-relations-hom-pres
Tagged Lean lemmas :
 - `Semigroup.RPreorder.hom_pres`
 - `Semigroup.LPreorder.hom_pres`
 - `Semigroup.JPreorder.hom_pres`
 - `Semigroup.HPreorder.hom_pres`
 - `Semigroup.REquiv.hom_pres`
 - `Semigroup.LEquiv.hom_pres`
 - `Semigroup.JEquiv.hom_pres`
 - `Semigroup.HEquiv.hom_pres`
 - `Semigroup.DEquiv.hom_pres`
Content : prove ≤R and 𝓡, say ≤L and 𝓛 holds by a similar argument.
Then, prove ≤𝓙 and 𝓙, then ≤𝓗 and 𝓗, then 𝓓.
Dependencies : greens-relations
-/

/-! ### Idempotent properties (Prop 1.4.1) -/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- An element `x` is 𝓡-below an idempotent `e` if and only if `x = e * x`. -/
theorem RPreorder.le_idempotent (x e : S) (h: IsIdempotentElem e) :
    (x ≤𝓡 e) ↔ (x = e * x) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h]
  · intro hl; use x
    rw [← WithOne.coe_inj] at hl; exact hl

/-- An element `x` is 𝓛-below an idempotent `e` if and only if `x = x * e`. -/
theorem LPreorder.le_idempotent (x e : S) (h: IsIdempotentElem e) :
    (x ≤𝓛 e) ↔ (x = x * e) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, mul_assoc, h]
  · intro hl; use x
    rw [← WithOne.coe_inj] at hl; exact hl

/-- An element is 𝓗-below an idempotent if and only if it is fixed by both left and right
multiplication. -/
theorem HPreorder.le_idempotent (x e : S) (h : IsIdempotentElem e) :
    (x ≤𝓗 e) ↔ (x = e * x ∧ x = x * e) := by
  simp [HPreorder, RPreorder.le_idempotent x e h, LPreorder.le_idempotent x e h]

/-- An element is 𝓗-below an idempotent if and only if it is a sandwich fixed point. -/
theorem HPreorder.le_idempotent' (x e : S) (he : IsIdempotentElem e) :
    x ≤𝓗 e ↔ e * x * e = x := by
  rw [HPreorder.le_idempotent x e he]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [← h₁, ← h₂]
  · intro h; constructor
    · nth_rw 2 [← h]
      simp_rw [← mul_assoc]; rw [he, h]
    · nth_rw 2 [← h]
      rw [mul_assoc, he, h]

/-!
### Morphisms

We prove that all of Green's preorders and equivalences are preserved under morphisms.
Note that these should quantify over `MulHomClass`.
-/

variable {S T : Type*} [Semigroup S] [Semigroup T]
variable {F : Type*} [FunLike F S T] [MulHomClass F S T]

/-- The 𝓡-preorder is preserved by semigroup morphisms. -/
theorem RPreorder.hom_pres (f : F) (x y : S) (h : x ≤𝓡 y) : f x ≤𝓡 f y := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => simp_all
  | coe z =>
    have heq : x = y * z := by
      rw [← WithOne.coe_inj, WithOne.coe_mul]
      exact hz
    rw [← WithOne.coe_mul, WithOne.coe_inj] at hz
    subst x
    simp

/-- The 𝓛-preorder is preserved by semigroup morphisms. -/
theorem LPreorder.hom_pres (f : F) (x y : S) (h : x ≤𝓛 y) : f x ≤𝓛 f y := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => simp_all
  | coe z =>
    have heq : x = z * y := by
      rw [← WithOne.coe_inj, WithOne.coe_mul]
      exact hz
    rw [← WithOne.coe_mul, WithOne.coe_inj] at hz
    subst x
    simp

/-- The 𝓙-preorder is preserved by semigroup morphisms. -/
theorem JPreorder.hom_pres (f : F) (x y : S) (h : x ≤𝓙 y) : f x ≤𝓙 f y := by
  obtain ⟨u, v, huv⟩ := h
  cases u with
  | one =>
    cases v with
    | one => simp_all
    | coe v =>
      have heq : x = y * v := by
        rw [← WithOne.coe_inj, WithOne.coe_mul]
        exact huv
      subst x
      simp
  | coe u =>
    cases v with
    | one =>
      have heq : x = u * y := by
        rw [← WithOne.coe_inj, WithOne.coe_mul]
        exact huv
      subst x
      simp
    | coe v =>
      have heq : x = u * y * v := by
        rw [← WithOne.coe_inj, WithOne.coe_mul]
        exact huv
      subst x
      simp

/-- The 𝓗-preorder is preserved by semigroup morphisms. -/
theorem HPreorder.hom_pres (f : F) (x y : S) (h : x ≤𝓗 y) : f x ≤𝓗 f y := by
  rw [HPreorder] at h ⊢
  exact ⟨RPreorder.hom_pres f x y h.1, LPreorder.hom_pres f x y h.2⟩

/-- The 𝓡 equivalence is preserved by semigroup morphisms. -/
theorem REquiv.hom_pres (f : F) (x y : S) (h : x 𝓡 y) : f x 𝓡 f y := by
  rw [REquiv] at h ⊢
  exact ⟨RPreorder.hom_pres f x y h.1, RPreorder.hom_pres f y x h.2⟩

/-- The 𝓛 equivalence is preserved by semigroup morphisms. -/
theorem LEquiv.hom_pres (f : F) (x y : S) (h : x 𝓛 y) : f x 𝓛 f y := by
  rw [LEquiv] at h ⊢
  exact ⟨LPreorder.hom_pres f x y h.1, LPreorder.hom_pres f y x h.2⟩

/-- The 𝓙 equivalence is preserved by semigroup morphisms. -/
theorem JEquiv.hom_pres (f : F) (x y : S) (h : x 𝓙 y) : f x 𝓙 f y := by
  rw [JEquiv] at h ⊢
  exact ⟨JPreorder.hom_pres f x y h.1, JPreorder.hom_pres f y x h.2⟩

/-- The 𝓗 equivalence is preserved by semigroup morphisms. -/
theorem HEquiv.hom_pres (f : F) (x y : S) (h : x 𝓗 y) : f x 𝓗 f y := by
  rw [HEquiv] at h ⊢
  exact ⟨HPreorder.hom_pres f x y h.1, HPreorder.hom_pres f y x h.2⟩

/-- The 𝓓 equivalence is preserved by semigroup morphisms. -/
theorem DEquiv.hom_pres (f : F) (x y : S) (h : x 𝓓 y) : f x 𝓓 f y := by
  rw [DEquiv] at h ⊢
  obtain ⟨z, hxz, hyz⟩ := h
  use f z
  exact ⟨REquiv.hom_pres f x z hxz, LEquiv.hom_pres f z y hyz⟩

end Semigroup
