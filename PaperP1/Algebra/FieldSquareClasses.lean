module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.NormNum

/-! # The actual square classes of a field as a vector space over F₂ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FieldSquareClasses

def doubles (F : Type*) [Field F] : AddSubgroup (Additive Fˣ) := (nsmulAddMonoidHom 2).range

abbrev Classes (F : Type*) [Field F] := Additive Fˣ ⧸ doubles F

instance classesModule (F : Type*) [Field F] : Module (ZMod 2) (Classes F) :=
  QuotientAddGroup.zmodModule (by intro u; exact ⟨u, rfl⟩)

def unitClass {F : Type*} [Field F] (u : Fˣ) : Classes F := QuotientAddGroup.mk (Additive.ofMul u)

theorem unitClass_mul {F : Type*} [Field F] (u v : Fˣ) :
    unitClass (u * v) = unitClass u + unitClass v := by
  unfold unitClass
  rw [ofMul_mul, QuotientAddGroup.mk_add]

theorem unitClass_zero_iff {F : Type*} [Field F] (u : Fˣ) : unitClass u = 0 ↔ IsSquare (u : F) := by
  rw [unitClass, QuotientAddGroup.eq_zero_iff]
  change (∃ v : Additive Fˣ, 2 • v = Additive.ofMul u) ↔ IsSquare (u : F)
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(v.toMul : F), ?_⟩
    have h := congrArg (fun z : Additive Fˣ ↦ (z.toMul : F)) hv
    simpa [pow_two] using h.symm
  · rintro ⟨v, hv⟩
    have hv₀ : v ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hv
      exact Units.ne_zero u hv
    refine ⟨Additive.ofMul (Units.mk0 v hv₀), ?_⟩
    change Additive.ofMul (Units.mk0 v hv₀ ^ 2) = Additive.ofMul u
    apply congrArg Additive.ofMul
    apply Units.ext
    simpa [pow_two] using hv.symm

def ofNonzero {F : Type*} [Field F] (a : F) (ha : a ≠ 0) : Classes F := unitClass (Units.mk0 a ha)

theorem ofNonzero_zero_iff {F : Type*} [Field F] (a : F) (ha : a ≠ 0) :
    ofNonzero a ha = 0 ↔ IsSquare a := unitClass_zero_iff _

theorem ofNonzero_mul {F : Type*} [Field F] (a b : F) (hab : a * b ≠ 0) :
    ofNonzero (a * b) hab =
      ofNonzero a (left_ne_zero_of_mul hab) + ofNonzero b (right_ne_zero_of_mul hab) := by
  unfold ofNonzero
  have hu : Units.mk0 (a * b) hab =
      Units.mk0 a (left_ne_zero_of_mul hab) * Units.mk0 b (right_ne_zero_of_mul hab) := by
    apply Units.ext
    rfl
  rw [hu, unitClass_mul]

theorem ofNonzero_one {F : Type*} [Field F] : ofNonzero (1 : F) one_ne_zero = 0 :=
  (ofNonzero_zero_iff (1 : F) one_ne_zero).mpr ⟨1, by simp⟩

theorem ofNonzero_prod {F ι : Type*} [Field F] (s : Finset ι) (f : ι → F) (hf : ∀ i, f i ≠ 0) :
    ofNonzero (∏ i ∈ s, f i) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hf i)) =
      ∑ i ∈ s, ofNonzero (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Finset.sum_empty] using (ofNonzero_one (F := F))
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, ofNonzero_mul, Finset.sum_insert ha]
    rw [ih]

theorem add_self {F : Type*} [Field F] (x : Classes F) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem add_zero_iff_eq {F : Type*} [Field F] (x y : Classes F) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = x + (y + y) := by rw [add_self]; exact (add_zero x).symm
      _ = (x + y) + y := (add_assoc _ _ _).symm
      _ = y := by rw [h]; exact zero_add y
  · intro h
    rw [h, add_self]

theorem pair_dependence_iff {F : Type*} [Field F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsSquare a ∨ IsSquare b ∨ IsSquare (a * b)) ↔
      ofNonzero a ha = 0 ∨ ofNonzero b hb = 0 ∨ ofNonzero a ha = ofNonzero b hb := by
  rw [← ofNonzero_zero_iff a ha, ← ofNonzero_zero_iff b hb,
    ← ofNonzero_zero_iff (a * b) (mul_ne_zero ha hb), ofNonzero_mul, add_zero_iff_eq]

end PaperP1.FieldSquareClasses
