module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! # Weight-at-most-two binary columns are actual labelled graph incidences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryIncidenceAugmentation

open Finset

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {P : Type*} [Fintype P] [DecidableEq P]

def augment : (P → ZMod 2) →ₗ[ZMod 2] (Option P → ZMod 2) where
  toFun f v := match v with | none => ∑ p, f p | some p => f p
  map_add' f g := by funext v; cases v <;> simp only [Pi.add_apply, sum_add_distrib]
  map_smul' a f := by funext v; cases v <;> simp only [Pi.smul_apply, ← smul_sum, RingHom.id_apply]

omit [DecidableEq P] in
theorem augment_none (f : P → ZMod 2) : augment f none = ∑ p, f p := rfl

omit [DecidableEq P] in
theorem augment_some (f : P → ZMod 2) (p : P) : augment f (some p) = f p := rfl

omit [DecidableEq P] in
theorem augment_injective : Function.Injective (augment (P := P)) := by
  intro f g h
  funext p
  exact congrFun h (some p)

omit [DecidableEq P] in
theorem ker_augment_comp {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (f : E →ₗ[ZMod 2] (P → ZMod 2)) : LinearMap.ker (augment.comp f) = LinearMap.ker f := by
  apply Submodule.ext
  intro e
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  exact ⟨fun h ↦ augment_injective (h.trans (map_zero augment).symm), fun h ↦ by rw [h, map_zero]⟩

def binaryColumn (S : Finset P) : P → ZMod 2 := fun p ↦ if p ∈ S then 1 else 0

def edgeColumn (a b : Option P) : Option P → ZMod 2 :=
  fun v ↦ (if v = a then 1 else 0) + if v = b then 1 else 0

theorem augmented_column_none (S : Finset P) : augment (binaryColumn S) none = (S.card : ZMod 2) := by
  simp [augment, binaryColumn]

theorem exists_edge (S : Finset P) (hS : S.card ≤ 2) :
    ∃ a b : Option P, augment (binaryColumn S) = edgeColumn a b := by
  classical
  by_cases hzero : S.card = 0
  · have he := card_eq_zero.mp hzero
    refine ⟨none, none, ?_⟩
    funext v
    cases v <;> simp [he, augment, binaryColumn, edgeColumn]; decide
  by_cases hone : S.card = 1
  · obtain ⟨p, rfl⟩ := card_eq_one.mp hone
    refine ⟨some p, none, ?_⟩
    funext v
    cases v with
    | none => rw [augmented_column_none]; simp [edgeColumn]
    | some q => simp [augment_some, binaryColumn, edgeColumn]
  have htwo : S.card = 2 := by omega
  obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.mp htwo
  refine ⟨some p, some q, ?_⟩
  funext v
  cases v with
  | none => rw [augmented_column_none]; simp [edgeColumn, hpq]; decide
  | some r =>
    rw [augment_some]
    by_cases hrp : r = p
    · subst r; simp [binaryColumn, edgeColumn, hpq]
    · by_cases hrq : r = q
      · subst r; simp [binaryColumn, edgeColumn, hrp]
      · simp [binaryColumn, edgeColumn, hrp, hrq]

def columnMap {J : Type*} [Fintype J] (S : J → Finset P) :
    (J → ZMod 2) →ₗ[ZMod 2] (P → ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (fun j ↦ binaryColumn (S j))

def incidenceMap {J : Type*} [Fintype J] (a b : J → Option P) :
    (J → ZMod 2) →ₗ[ZMod 2] (Option P → ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (fun j ↦ edgeColumn (a j) (b j))

theorem exists_incidence_model {J : Type*} [Fintype J] (S : J → Finset P) (hS : ∀ j, (S j).card ≤ 2) :
    ∃ a b : J → Option P, incidenceMap a b = augment.comp (columnMap S) ∧
      LinearMap.ker (incidenceMap a b) = LinearMap.ker (columnMap S) := by
  choose a b h using fun j ↦ exists_edge (S j) (hS j)
  have he : incidenceMap a b = augment.comp (columnMap S) := by
    apply LinearMap.ext
    intro w
    simp only [incidenceMap, columnMap, Fintype.linearCombination_apply, LinearMap.comp_apply,
      map_sum, map_smul]
    apply sum_congr rfl
    intro j _hj
    rw [h j]
  exact ⟨a, b, he, he ▸ ker_augment_comp (columnMap S)⟩

end PaperP1.BinaryIncidenceAugmentation
