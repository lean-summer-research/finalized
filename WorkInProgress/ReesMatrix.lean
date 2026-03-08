import MyProject.Green.Location
import MyProject.Ideals
import MyProject.Idempotent

/-! # Rees Matrix Semigroups -/

namespace Semigroup

section RegularSemigroup

variable {S : Type*} [Semigroup S]

def isRegularElem (x : S) : Prop :=
  ∃ y : S, x * y * x = x

def isRegularSemigroup : Prop :=
  ∀ x : S, isRegularElem x

end RegularSemigroup

universe u v w uS

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

/-! ## Rees Matrix Theorem: Simple iff Rees -/

section ReesTheorem

variable {S : Type uS} [Finite S] [SimpleSemigroup S] [Inhabited S]

open Semigroup

/-- Forward direction of the Rees Matrix Theorem:
A finite simple semigroup is isomorphic to a Rees matrix semigroup (without zero). -/
theorem simple_iff_rees_forward :
    ∃ (I J G : Type uS) (_ : Group G) (P : I → J → G),
      Nonempty (S ≃* Rees P) := by
  -- we open classical logic throughout so we can freely pick elements without constructing them explicitly
  classical
  -- the defining property of a simple semigroup is that sas = s ∀ a∈S,
  -- e.g. there are no proper two-sided ideals, e.g. every pair of elements is j-equivalent.
  -- jpreorder.ofsimple proves both directions (x ≤𝓙 y and y ≤𝓙 x) from simplicity:
  have h_j_all : ∀ x y : S, x 𝓙 y := by
    intro x y
    exact ⟨JPreorder.ofSimple x y, JPreorder.ofSimple y x⟩
  -- in a finite semigroup D and J relations coincide:
  have h_single_d : ∀ x y : S, x 𝓓 y := by
    intro x y
    exact JEquiv.to_dEquiv (h_j_all x y)
  have h_idem : ∃ e : S, IsIdempotentElem e := by
    classical
    obtain ⟨m, hm⟩ := Semigroup.exists_idempotent_pow (default : S)
    exact ⟨(default : S) ^ m, hm⟩ -- any element raised to some power is idempotent
  obtain ⟨e, he⟩ := h_idem
  have h_reg : @isRegularSemigroup S _ := by
    sorry -- proposition 1.9
  -- visualize the single D-class as a rectangular grid of R-classes (rows) by L-classes
  -- (columns), with each cell being an H-class. WLOG place e in the (1,1) position of the grid. the h-class
  -- ⟦e⟧𝓗 = {x ∈ S | x 𝓗 e} is a maximal subgroup of S, which we become our Rees Matrix group G. in lean, G is a subtype of S,
  -- so elements of G coerce to S via the standard subtype coercion ↑G = G.val.
  -- we use `leti` rather than `have` for hg_group because we need lean to register the
  -- group instance at higher priority as a local typeclass. if we used `have`, lean might
  -- pick a different mul g instance downstream, causing `↑(a * b : g) =
  -- ↑a * ↑b to fail. with `leti`, the instance is transparent and definitionally correct,
  -- so that identity becomes rfl.
  let G := {x : S // x ∈ ⟦e⟧𝓗}
  letI hG_group : Group G := HEquiv.group_of_idempotent he
  -- the R-classes of S form the index set I, and the L-classes form J. in lean, we
  -- formalize a congruence relation as a setoid (a type bundling a relation with a proof
  -- it is an equivalence), and then take the quotient type. Quotient rSetoid is the type
  -- whose terms are R-equivalence classes, and similarly for Quotient lSetoid.
  -- elements of I are of the form Quotient.mk rSetoid x (the R-class of x), written ⟦x⟧.
  let rSetoid : Setoid S := ⟨(· 𝓡 ·), REquiv.isEquivalence⟩
  let lSetoid : Setoid S := ⟨(· 𝓛 ·), LEquiv.isEquivalence⟩
  let I := Quotient rSetoid
  let J := Quotient lSetoid
  -- for each L-class J we need a representative r_j that lies in the R-class of e, i.e.,
  -- r_j is R-related to e. in the textbook's grid picture, this is the element in row 1
  -- (the R-class of e) and column J. we prove such an element exists using the D-class
  -- structure: since e and any representative Y of J are D-related, the definition of 𝓓
  -- unpacks as ∃ Z, e 𝓡 Z ∧ Z 𝓛 Y. that Z is exactly what we want.
  -- Quotient.exists_rep destructs the quotient type J into a concrete element Y with
  -- Quotient.mk lSetoid Y = J.
  -- Quotient.sound converts the semigroup relation Z 𝓛 Y into the propositional equality
  -- Quotient.mk lSetoid Z = Quotient.mk lSetoid Y
  have h_r_exists :
      ∀ j : J, ∃ z : S, z ∈ ⟦e⟧𝓡 ∧ Quotient.mk lSetoid z = j := by
    intro j
    obtain ⟨y, rfl⟩ := Quotient.exists_rep j
    have hD : e 𝓓 y := h_single_d e y
    rcases hD with ⟨z, hzR, hzL⟩
    refine ⟨z, ?_, ?_⟩
    · -- hzR says e 𝓡 z (i.e., z is in the R-class of e), so z 𝓡 e by symmetry.
      exact REquiv.symm hzR
    · -- Quotient.sound turns the L-relation hzL : z 𝓛 y into an equality of quotient elements
      exact Quotient.sound hzL
  -- classical.choose picks a specific z satisfying h_r_exists j for each j, giving
  -- us the function r : J → S. Classical.choose_spec extracts the proof that this
  -- choice satisfies both conditions (r_j ∈ ⟦e⟧𝓡 and Quotient.mk lSetoid (r_j) = j).
  let r : J → S := fun j => Classical.choose (h_r_exists j)
  have hr_repr :
      ∀ j : J, r j ∈ ⟦e⟧𝓡 ∧ Quotient.mk lSetoid (r j) = j := by
    intro j
    exact Classical.choose_spec (h_r_exists j)
  -- dual story for s_i. for each R-class I we pick s_i in the L-class of e (column 1,
  -- row i in the grid). this time the D-class gives us ∃ Z, X 𝓡 Z ∧ Z 𝓛 E, and Z works
  have h_s_exists :
      ∀ i : I, ∃ z : S, z ∈ ⟦e⟧𝓛 ∧ Quotient.mk rSetoid z = i := by
    intro i
    obtain ⟨x, rfl⟩ := Quotient.exists_rep i
    have hD : x 𝓓 e := h_single_d x e
    rcases hD with ⟨z, hzR, hzL⟩
    refine ⟨z, ?_, ?_⟩
    · exact hzL
    · -- hzR : x 𝓡 z, but we need Quotient.mk rSetoid z = Quotient.mk rSetoid x,
      -- which requires rSetoid.r z x, i.e., z 𝓡 x. REquiv.symm flips the direction.
      exact Quotient.sound (REquiv.symm hzR)
  let s : I → S := fun i => Classical.choose (h_s_exists i)
  have hs_repr :
      ∀ i : I, s i ∈ ⟦e⟧𝓛 ∧ Quotient.mk rSetoid (s i) = i := by
    intro i
    exact Classical.choose_spec (h_s_exists i)
  -- the Rees matrix is p(i, j) = r_j * s_i. we need to show this product lands in
  -- G = ⟦e⟧𝓗, meaning r_j * s_i is both R-related and L-related to e.
  -- for the R-relation: right-multiplication can only drop in the R-preorder, so
  -- r_j * s_i ≤𝓡 r_j (RPreorder.mul_right_self). since S is a single J-class,
  -- r_j * s_i 𝓙 r_j. in a finite semigroup, ≤𝓡 together with 𝓙 implies full 𝓡-equivalence
  -- (REquiv.of_rPreorder_and_jEquiv). then transitivity with hrr : r_j 𝓡 e gives the result.
  have hP_in_G : ∀ i j, r j * s i ∈ ⟦e⟧𝓗 := by
    intro i j
    have hrR : r j 𝓡 e := (hr_repr j).1
    have hsL : s i 𝓛 e := (hs_repr i).1
    have hR : r j * s i 𝓡 e := by
      have hle : r j * s i ≤𝓡 r j := RPreorder.mul_right_self
      have hj : r j * s i 𝓙 r j := h_j_all (r j * s i) (r j)
      exact REquiv.trans (REquiv.of_rPreorder_and_jEquiv hle hj) hrR
    have hL : r j * s i 𝓛 e := by
      have hle : r j * s i ≤𝓛 s i := LPreorder.mul_left_self
      have hj : r j * s i 𝓙 s i := h_j_all (r j * s i) (s i)
      exact LEquiv.trans (LEquiv.of_lPreorder_and_jEquiv hle hj) hsL
    have hH : r j * s i 𝓗 e := by
      have hRL : r j * s i 𝓡 e ∧ r j * s i 𝓛 e := ⟨hR, hL⟩
      exact (HEquiv.iff_rEquiv_and_lEquiv (r j * s i) e).2 hRL
    exact hH
  -- P is the Rees matrix: P(i, j) is the element r_j * s_i packed as a subtype of G.
  -- the coercion ↑(P(i, j)) : S will later unfold to r_j * s_i via `simp [P]`.
  let P : I → J → G := fun i j => ⟨r j * s i, hP_in_G i j⟩
  -- now we prove that every x ∈ S has a representation x = s_i * ↑g * r_j for some
  -- unique triple (i, j, g). this is the coordinate system for the isomorphism.
  -- to find the coordinates of x, define i and j as the R-class and L-class of x
  -- respectively (just Quotient.mk applied to x). then use these to prove existence of g.
  -- the argument goes in two steps using Green's lemma:
  --   (a) right-mult by r_j is a surjection from ⟦s_i⟧𝓗 onto ⟦x⟧𝓗, giving some h with h * r_j = x.
  --   (b) left-mult by s_i is a surjection from ⟦e⟧𝓗 = G onto ⟦s_i⟧𝓗, giving g with s_i * g = h.
  -- combining: x = h * r_j = s_i * g * r_j.
  -- the surjectivity lemmas (surjon_hClass) work on H-class membership, so we first need to
  -- know that s_i * r_j is H-related to x. this comes from the location theorem
  -- (mul_in_inter_iff_exists_idempotent) applied backwards: since e is an idempotent in
  -- ⟦r_j⟧𝓡 ∩ ⟦s_i⟧𝓛, the product s_i * r_j lands in ⟦s_i⟧𝓡 ∩ ⟦r_j⟧𝓛
  have h_decomp : ∀ x : S, ∃ (i : I) (j : J) (g : G), x = s i * ↑g * r j := by
    intro x
    -- define i and j as the R-class and L-class of x
    let i := Quotient.mk rSetoid x
    let j := Quotient.mk lSetoid x
    use i, j
    -- Quotient.exact inverts Quotient.sound: since (hs_repr i).2 says Quotient.mk rSetoid (s i) = i,
    -- which is the same i we just defined as Quotient.mk rSetoid x, exactness gives s i 𝓡 x.
    have h_si_R : s i 𝓡 x := Quotient.exact (hs_repr i).2
    have h_rj_L : r j 𝓛 x := Quotient.exact (hr_repr j).2
    have hrR : r j 𝓡 e := (hr_repr j).1
    have hsL : s i 𝓛 e := (hs_repr i).1
    -- LPreorder.le_idempotent says x ≤𝓛 e iff x * e = x. since s i ≤𝓛 e, this gives s i * e = s i.
    -- we need this to set up the surjection hypothesis for the second Green's lemma call.
    have h_sie : s i * e = s i := (LPreorder.le_idempotent he (s i)).mp hsL.1
    -- the location theorem (backward direction): to get s i * r j ∈ ⟦s i⟧𝓡 ∩ ⟦r j⟧𝓛,
    -- it suffices to find an idempotent in ⟦r j⟧𝓡 ∩ ⟦s i⟧𝓛. that idempotent is e:
    -- e ∈ ⟦r j⟧𝓡 because r j 𝓡 e (hrr), meaning e is in the R-class of r j.
    -- and likewise e ∈ ⟦s i⟧𝓛 because s i 𝓛 e (hsl), meaning e is in the L-class of s i.
    have h_sirj_mem : s i * r j ∈ ⟦s i⟧𝓡 ∩ ⟦r j⟧𝓛 :=
      (mul_in_inter_iff_exists_idempotent (s i) (r j)).2 ⟨e, he, hrR.symm, hsL.symm⟩
    -- h_sirj_mem.1 says s i * r j 𝓡 s i
    -- chaining with h_si_R (s i 𝓡 x) gives s i * r j 𝓡 x, and similarly for 𝓛.
    -- HEquiv.iff_rEquiv_and_lEquiv packages both as H-equivalence.
    have h_sirj_H : s i * r j 𝓗 x :=
      (HEquiv.iff_rEquiv_and_lEquiv _ _).2
        ⟨REquiv.trans h_sirj_mem.1 h_si_R, LEquiv.trans h_sirj_mem.2 h_rj_L⟩
    -- h_sir_rsi : s i 𝓡 s i * r j is the hypothesis that surjon_hclass needs to apply Green's lemma (the R-class bijection preserves H-classes).
    have h_sir_Rsi : s i 𝓡 s i * r j := h_sirj_mem.1.symm
    -- surjon_hclass says: if s i 𝓡 s i * r j and s i * r j = s i * r j (rfl), then right-mult
    -- by r j is surjective from ⟦s i⟧𝓗 onto ⟦s i * r j⟧𝓗. since x 𝓗 s i * r j,
    --we get some h ∈ ⟦s i⟧𝓗 with h * r j = x.
    obtain ⟨h, hh_mem, hh_eq⟩ :=
      h_sir_Rsi.surjOn_hClass rfl h_sirj_H.symm
    -- surjon_hclass returns hh_eq as a lambda application (fun w ↦ w * r j) h = x,
    -- which lean will not rewrite with directly since rw is syntactic. we introduce
    -- hh_eq' with type h * r j = x, which lean accepts via definitional equality (beta).
    have hh_eq' : h * r j = x := hh_eq
    -- now apply Green's lemma in the L-direction: left-mult by s i is surjective from
    -- ⟦e⟧𝓗 = G onto ⟦s i⟧𝓗. the surjectivity condition is s i 𝓛 e and
    -- s i * e = s i, together giving the bijection s i * · from ⟦e⟧𝓗 to ⟦s i⟧𝓗.
    -- since h ∈ ⟦s i⟧𝓗, we get g ∈ G with s i * g = h.
    obtain ⟨g, hg_mem, hg_eq⟩ :=
      hsL.symm.surjOn_hClass h_sie hh_mem
    have hg_eq' : s i * g = h := hg_eq
    -- wrap g together with hg_mem (the proof that g ∈ ⟦e⟧𝓗) into a subtype element of g.
    exact ⟨⟨g, hg_mem⟩, show x = s i * ↑(⟨g, hg_mem⟩ : G) * r j from by
      change x = s i * g * r j
      calc x = h * r j       := hh_eq'.symm
           _ = s i * g * r j := by rw [hg_eq']⟩

  -- uniqueness of the representation x = s i * g * r j.
  -- the proof has three parts, each using a different injectivity or cancellation argument.
  have h_decomp_unique : ∀ x (i i' : I) (j j' : J) (g g' : G),
      x = s i * g * r j → x = s i' * g' * r j' →
      i = i' ∧ j = j' ∧ g = g' := by
    intro x i i' j j' g g' hx hx'
    have hrR  : r j  𝓡 e := (hr_repr j).1
    have hrR' : r j' 𝓡 e := (hr_repr j').1
    have hsL  : s i  𝓛 e := (hs_repr i).1
    have hsL' : s i' 𝓛 e := (hs_repr i').1
    have h_sie  : s i  * e = s i  := (LPreorder.le_idempotent he (s i )).mp hsL.1
    have h_sie' : s i' * e = s i' := (LPreorder.le_idempotent he (s i')).mp hsL'.1
    -- g.prop is the proof that ↑g ∈ ⟦e⟧𝓗, i.e., (↑g : s) 𝓗 e. from this we extract
    -- the R-component (hgr : ↑g 𝓡 e) and L-component using the field accessors to_rEquiv / to_lEquiv.
    have hgH  : (↑g  : S) 𝓗 e := g.prop
    have hgH' : (↑g' : S) 𝓗 e := g'.prop
    have hgR  : (↑g  : S) 𝓡 e := hgH.to_rEquiv
    have hgR' : (↑g' : S) 𝓡 e := hgH'.to_rEquiv
    -- to show i = i', we trace x back to its R-class from both decompositions.
    -- from hx: x = s i * ↑g * r j. right-multiplication by r j drops in R (RPreorder.mul_right_self),
    -- and since s is a single J-class, RPreorder + JEquiv gives full R-equivalence
    -- (REquiv.of_rPreorder_and_jEquiv). so s i * ↑g * r j 𝓡 s i * ↑g.
    -- then: ↑g 𝓡 e (hgr) so by left-compatibility of R (REquiv.lmult_compat),
    -- s i * ↑g 𝓡 s i * e = s i. combining: x 𝓡 s i.
    -- by the same argument, x 𝓡 s i'. so s i 𝓡 s i' by transitivity and symmetry.
    -- to convert that semigroup relation into an equality of quotient elements, we use Quotient.sound.
    -- the repr fact (hs_repr i).2 says Quotient.mk rSetoid (s i) = i,
    -- so rewriting on both sides of the quotient equality turns it into i = i'.
    have h_x_Rsi : x 𝓡 s i := by
      have h_sig_Rsi : s i * ↑g 𝓡 s i := by
        have h := REquiv.lmult_compat hgR (s i); rw [h_sie] at h; exact h
      rw [hx]
      exact (REquiv.of_rPreorder_and_jEquiv RPreorder.mul_right_self
        (h_j_all _ _)).trans h_sig_Rsi
    have h_x_Rsi' : x 𝓡 s i' := by
      have h_sig_Rsi' : s i' * ↑g' 𝓡 s i' := by
        have h := REquiv.lmult_compat hgR' (s i'); rw [h_sie'] at h; exact h
      rw [hx']
      exact (REquiv.of_rPreorder_and_jEquiv RPreorder.mul_right_self
        (h_j_all _ _)).trans h_sig_Rsi'
    have hi_eq : i = i' := by
      have h := @Quotient.sound S rSetoid _ _ (h_x_Rsi.symm.trans h_x_Rsi')
      rw [(hs_repr i).2, (hs_repr i').2] at h; exact h
    -- dual argument for j = j'. from x = s i * ↑g * r j, left-multiplication always drops
    -- in the L-preorder (LPreorder.mul_left_self), so s i * ↑g * r j ≤𝓛 r j.
    -- combined with the single J-class, we get x 𝓛 r j and x 𝓛 r j'. so r j 𝓛 r j',
    -- and the same Quotient.sound trick with (hr_repr j).2 turns that into j = j'.
    have h_x_Lrj : x 𝓛 r j := by
      rw [hx]
      exact LEquiv.of_lPreorder_and_jEquiv LPreorder.mul_left_self (h_j_all _ _)
    have h_x_Lrj' : x 𝓛 r j' := by
      rw [hx']
      exact LEquiv.of_lPreorder_and_jEquiv LPreorder.mul_left_self (h_j_all _ _)
    have hj_eq : j = j' := by
      have h := @Quotient.sound S lSetoid _ _ (h_x_Lrj.symm.trans h_x_Lrj')
      rw [(hr_repr j).2, (hr_repr j').2] at h; exact h
    -- now that i = i' and j = j', cancel them to get s i * ↑g * r j = s i * ↑g' * r j.
    -- we cancel r j on the right using injectivity of (· * r j) restricted to ⟦s i⟧𝓗
    -- (requiv.injon_HClass). but we first need to know s i * ↑g and s i * ↑g' are both in
    -- ⟦s i⟧𝓗. we show this again via the location theorem: since ↑g 𝓡 e and s i 𝓛 e,
    -- e ∈ ⟦↑g⟧𝓡 ∩ ⟦s i⟧𝓛, so s i * ↑g ∈ ⟦s i⟧𝓡 ∩ ⟦↑g⟧𝓛. the R-component
    -- ⟦s i⟧𝓛 (since ↑g 𝓡 e and s i 𝓛 e), so s i * ↑g ∈ ⟦s i⟧𝓡 ∩ ⟦↑g⟧𝓛. the R-component
    -- gives s i * ↑g 𝓡 s i, and the L-component chained with hgh.to_lEquiv and hsl.symm
    -- gives s i * ↑g 𝓛 s i, so s i * ↑g 𝓗 s i.
    -- after canceling r j we have s i * ↑g = s i * ↑g'. we cancel s i on the left using
    -- injectivity of (s i * ·) on ⟦e⟧𝓗 (LEquiv.injOn_hClass with hsl.symm and h_sie).
    -- the result is (↑g : s) = ↑g', and subtype.ext lifts this to the g-equality g = g'.
    refine ⟨hi_eq, hj_eq, ?_⟩
    have h_eq : s i * ↑g * r j = s i * ↑g' * r j := by
      have := hx.symm.trans hx'; rwa [← hi_eq, ← hj_eq] at this
    have h_sir_Rsi : s i 𝓡 s i * r j :=
      (((mul_in_inter_iff_exists_idempotent (s i) (r j)).2
        ⟨e, he, hrR.symm, hsL.symm⟩).1).symm
    have h_sig_mem : s i * ↑g ∈ ⟦s i⟧𝓗 := by
      show s i * ↑g 𝓗 s i
      have h := (mul_in_inter_iff_exists_idempotent (s i) (↑g)).2
        ⟨e, he, hgR.symm, hsL.symm⟩
      exact (HEquiv.iff_rEquiv_and_lEquiv _ _).2
        ⟨h.1, h.2.trans (hgH.to_lEquiv.trans hsL.symm)⟩
    have h_sig'_mem : s i * ↑g' ∈ ⟦s i⟧𝓗 := by
      show s i * ↑g' 𝓗 s i
      have h := (mul_in_inter_iff_exists_idempotent (s i) (↑g')).2
        ⟨e, he, hgR'.symm, hsL.symm⟩
      exact (HEquiv.iff_rEquiv_and_lEquiv _ _).2
        ⟨h.1, h.2.trans (hgH'.to_lEquiv.trans hsL.symm)⟩
    have h_sig_eq : s i * ↑g = s i * ↑g' :=
      (REquiv.injOn_hClass h_sir_Rsi rfl) h_sig_mem h_sig'_mem h_eq
    have h_g_eq : (↑g : S) = ↑g' :=
      (LEquiv.injOn_hClass hsL.symm h_sie) hgH hgH' h_sig_eq
    exact Subtype.ext h_g_eq
  -- classical.choose (via the `choose` tactic) destructs the ∀ x, ∃ i j g, ... in h_decomp
  -- into three choice functions i_of, j_of, g_of and a proof h_decomp that the equation holds.
  -- the map φ then assembles these into a rees matrix element for each x.
  choose i_of j_of g_of h_decomp using h_decomp
  let φ : S → Rees P := fun x => ⟨i_of x, j_of x, g_of x⟩
  -- multiplicativity of φ. in rees matrix, multiplication is defined as
  -- (i, g, j) * (i', g', j') = (i, g * p(i', j) * g', j'). so φ(x) * φ(y) should have
  -- first index i_of x, last index j_of y, and middle element g_of x * p(i_of y, j_of x) * g_of y.
  -- the key insight is that the "inner" product r(j_of x) * s(i_of y) is exactly p(i_of y, j_of x).
  --
  -- a key lean mechanic here: ↑(a * b : g) = ↑a * ↑b holds by rfl because we used `leti`
  -- for hg_group, making the mul g instance transparent. if we had used `have`, bad things would happen
  have h_mul : ∀ x y : S, φ (x * y) = φ x * φ y := by
    intro x y
    have hx : x = s (i_of x) * g_of x * r (j_of x) := h_decomp x
    have hy : y = s (i_of y) * g_of y * r (j_of y) := h_decomp y
    have hxy : x * y = s (i_of (x * y)) * g_of (x * y) * r (j_of (x * y)) := h_decomp (x * y)
    let ix  : I := i_of x
    let jx  : J := j_of x
    let gx  : G := g_of x
    let iy  : I := i_of y
    let jy  : J := j_of y
    let gy  : G := g_of y
    -- the candidate decomposition of x * y has first index ix, last index jy,
    -- and group element gx * p(iy, jx) * gy, where the p factor is the product
    -- term r jx * s iy that appears in the middle of the flat product.
    let icand : I := ix
    let jcand : J := jy
    let gcand : G := gx * P iy jx * gy
    have h_candidate :
        x * y = s icand * gcand * r jcand := by
      have hx' : x = s ix * ↑gx * r jx := by simpa [ix, jx, gx] using hx
      have hy' : y = s iy * ↑gy * r jy := by simpa [iy, jy, gy] using hy
      -- ↑(p iy jx) unfolds to r jx * s iy by the definition of p.
      have hP_val : (↑(P iy jx) : S) = r jx * s iy := by simp [P]
      -- the coercion ↑(a * b : g) = ↑a * ↑b holds by rfl (see comment above about leti).
      have hcoe : ∀ (a b : G), (↑(a * b) : S) = ↑a * ↑b := fun _ _ => rfl
      -- expand the coercion of gcand step by step, distributing ↑ through multiplication.
      have hgcand : (↑gcand : S) = ↑gx * (r jx * s iy) * ↑gy :=
        calc (↑gcand : S)
            = ↑(gx * P iy jx * gy)      := rfl
          _ = ↑(gx * P iy jx) * ↑gy     := hcoe _ _
          _ = ↑gx * ↑(P iy jx) * ↑gy    := by rw [hcoe]
          _ = ↑gx * (r jx * s iy) * ↑gy := by rw [hP_val]
      -- flatten x * y into a fully expanded product in s using mul_assoc.
      have h1 : x * y = s ix * ↑gx * r jx * s iy * ↑gy * r jy := by
        calc x * y = (s ix * ↑gx * r jx) * (s iy * ↑gy * r jy) := by rw [hx', hy']
          _ = s ix * ↑gx * r jx * s iy * ↑gy * r jy := by simp [mul_assoc]
      -- fold back using hgcand. the r jx * s iy in the middle is the p value,
      -- and reassociation (mul_assoc) closes the goal.
      calc x * y
            = s ix * ↑gx * r jx * s iy * ↑gy * r jy := h1
          _ = s icand * ↑gcand * r jcand := by
                rw [hgcand]
                simp [icand, jcand, mul_assoc]
    -- h_decomp_unique identifies the canonical triple (i_of (x*y), j_of (x*y), g_of (x*y))
    -- with the candidate triple (icand, jcand, gcand) since both are valid decompositions of x*y.
    have huniq :=
      h_decomp_unique
        (x * y)
        (i_of (x * y)) icand
        (j_of (x * y)) jcand
        (g_of (x * y)) gcand
        hxy h_candidate
    rcases huniq with ⟨hi_eq, hj_eq, hg_eq⟩
    -- φ(x * y) = ⟨i_of (x*y), j_of (x*y), g_of (x*y)⟩. by the uniqueness equalities, this
    -- equals ⟨icand, jcand, gcand⟩ = ⟨ix, jy, gx * p iy jx * gy⟩.
    -- φ(x) * φ(y) in the Rees matrix is by rees.mul_def: ⟨ix, jx, gx⟩ * ⟨iy, jy, gy⟩ = ⟨ix, jy, gx * p iy jx * gy⟩
    have h_rhs :
        φ x * φ y =
          (⟨ix, jy, gx * P iy jx * gy⟩ : Rees P) := by
      simp [φ, Rees.mul_def, ix, jx, gx, iy, jy, gy]
    have h_lhs :
        φ (x * y) =
          (⟨ix, jy, gx * P iy jx * gy⟩ : Rees P) := by
      simp [φ, hi_eq, hj_eq, hg_eq, ix, jx, gx, iy, jy, gy, icand, jcand, gcand]
    simp [h_lhs, h_rhs]
  -- injectivity: if φ(x) = φ(y) in rees p then all three components agree.
  -- congr_arg rees.i/j/g extracts the equalities of individual struct fields.
  -- then h_decomp gives x = s(i_of x) * g_of x * r(j_of x), and substituting
  -- the equal components (hi, hj, hg) turns the right-hand side into the decomposition of y.
  have h_inj : Function.Injective φ := by
    intro x y hxy
    have hi : i_of x = i_of y := by
      simpa [φ] using congrArg Rees.i hxy
    have hj : j_of x = j_of y := by
      simpa [φ] using congrArg Rees.j hxy
    have hg : g_of x = g_of y := by
      simpa [φ] using congrArg Rees.g hxy
    have hx : x = s (i_of x) * g_of x * r (j_of x) := h_decomp x
    have hy : y = s (i_of y) * g_of y * r (j_of y) := h_decomp y
    calc
      x = s (i_of x) * g_of x * r (j_of x) := hx
      _ = s (i_of y) * g_of y * r (j_of y) := by simp [hi, hj, hg]
      _ = y                                 := by symm; exact hy
  -- surjectivity: given any z = (i, j, g) ∈ rees p, the preimage is s z.i * z.g.val * r z.j.
  -- h_decomp gives the canonical triple for this element. h_decomp_unique compares it
  -- with the obvious decomposition (z.i, z.j, z.g) and identifies all components.
  -- we use z.g.val rather than ↑z.g to help lean resolve the subtype coercion
  have h_right_inv : ∀ z : Rees P, φ (s z.i * z.g.val * r z.j) = z := by
    intro z
    have hcanon := h_decomp (s z.i * z.g.val * r z.j)
    have huniq := h_decomp_unique
        (s z.i * z.g.val * r z.j)
        (i_of (s z.i * z.g.val * r z.j)) z.i
        (j_of (s z.i * z.g.val * r z.j)) z.j
        (g_of (s z.i * z.g.val * r z.j)) z.g
        hcanon rfl
    rcases huniq with ⟨hi_eq, hj_eq, hg_eq⟩
    simp only [φ, hi_eq, hj_eq, hg_eq]
  have h_surj : Function.Surjective φ :=
    fun z => ⟨s z.i * z.g.val * r z.j, h_right_inv z⟩
  -- assemble the mulequiv. we have all the required fields:
  --   tofun = φ, the isomorphism forward direction.
  --   invfun = the inverse
  --   left_inv = (h_decomp x).symm: the decomposition equation x = s(i_of x) * g_of x * r(j_of x)
  --     rearranges to s(i_of x) * g_of x * r(j_of x) = x, which is exactly left_inv(φ(x)) = x
  --     since invfun (φ x) = s(i_of x) * (g_of x).val * r(j_of x) = x.
  --   right_inv = h_right_inv.
  --   map_mul' = h_mul.
  -- the final refine closes the existential by providing i, j, g, hg_group, p, and the
  -- nonempty wrapper around iso.
  let iso : S ≃* Rees P :=
    { toFun     := φ
      invFun    := fun z => s z.i * z.g.val * r z.j
      left_inv  := fun x => (h_decomp x).symm
      right_inv := h_right_inv
      map_mul'  := h_mul }
  refine ⟨I, J, G, hG_group, P, ⟨iso⟩⟩

end ReesTheorem

end Semigroup
