module

public import PaperP1.Affine.IndependentRows
public import PaperP1.Algebra.QuotientRank
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Exact affine probabilities after a realizable old linear observation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset PaperP1.Algebra PaperP1.Probability

local instance conditionalMassPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance conditionalMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]

local instance conditionalDualFinite : Finite (V →ₗ[𝔽₂] 𝔽₂) :=
  Finite.of_injective (fun f : V →ₗ[𝔽₂] 𝔽₂ ↦ (f : V → 𝔽₂)) DFunLike.coe_injective

local instance conditionalSubspaceFintype (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) : Fintype S := Fintype.ofFinite _

def oldObservationMass (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V) : ℝ :=
  finiteExpectation (uniformFiniteProbability V).weight (fun v ↦ if effectiveEvent W a v then 1 else 0)

def conditionalAffineMass {β : Type*} [Fintype β]
    (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V) (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) : ℝ :=
  finiteExpectation (uniformFiniteProbability V).weight
    (fun v ↦ if effectiveEvent W a v ∧ A v = b then 1 else 0) / oldObservationMass W a

theorem oldObservationMass_eq (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V) :
    oldObservationMass W a = (2 ^ Module.finrank 𝔽₂ W : ℝ)⁻¹ := by
  rw [oldObservationMass, effective_marginal, card_eq_two_pow_finrank (V := W)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem oldObservationMass_pos (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V) : 0 < oldObservationMass W a := by
  rw [oldObservationMass_eq]
  positivity

omit [Fintype V] in
theorem effectiveEvent_sup_iff (W S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a v : V) :
    effectiveEvent (W ⊔ S) a v ↔ effectiveEvent W a v ∧ effectiveEvent S a v := by
  constructor
  · intro h
    exact ⟨fun w ↦ h ⟨w.val, (show W ≤ W ⊔ S from le_sup_left) w.property⟩,
      fun s ↦ h ⟨s.val, (show S ≤ W ⊔ S from le_sup_right) s.property⟩⟩
  · rintro ⟨hW, hS⟩ ⟨f, hf⟩
    obtain ⟨w, hw, s, hs, rfl⟩ := Submodule.mem_sup.mp hf
    change w v + s v = w a + s a
    rw [hW ⟨w, hw⟩, hS ⟨s, hs⟩]

omit [Fintype V] in
theorem effectiveEvent_change_source (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) {a w : V}
    (hw : effectiveEvent W a w) (v : V) : effectiveEvent W a v ↔ effectiveEvent W w v := by
  constructor <;> intro h s
  · exact (h s).trans (hw s).symm
  · exact (h s).trans (hw s)

variable {β : Type*} [Fintype β]

theorem conditionalAffineMass_nonneg (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V)
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) : 0 ≤ conditionalAffineMass W a A b := by
  unfold conditionalAffineMass
  apply div_nonneg _ (oldObservationMass_pos W a).le
  unfold finiteExpectation
  apply sum_nonneg
  intro v _
  exact mul_nonneg ((uniformFiniteProbability V).weight_nonneg v) (by dsimp; split_ifs <;> norm_num)

theorem conditionalAffineMass_le_one (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V)
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) : conditionalAffineMass W a A b ≤ 1 := by
  apply (div_le_one (oldObservationMass_pos W a)).mpr
  unfold oldObservationMass finiteExpectation
  apply sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ ((uniformFiniteProbability V).weight_nonneg v)
  by_cases hv : effectiveEvent W a v <;> by_cases hb : A v = b <;> simp [hv, hb]

theorem conditionalAffineMass_of_witness (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V)
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) (w : V)
    (hw : effectiveEvent W a w ∧ A w = b) :
    conditionalAffineMass W a A b =
      (2 ^ Module.finrank 𝔽₂ (W.comap (relationMap A)) : ℝ) / (2 ^ Fintype.card β : ℝ) := by
  have hevent (v : V) : (effectiveEvent W a v ∧ A v = b) ↔
      effectiveEvent (W ⊔ effectiveRowSpace A) w v := by
    rw [effectiveEvent_sup_iff, effectiveEvent_change_source W hw.1 v, effectiveRowEvent_iff, hw.2]
  have hjoint : finiteExpectation (uniformFiniteProbability V).weight
      (fun v ↦ if effectiveEvent W a v ∧ A v = b then (1 : ℝ) else 0) =
        (2 ^ Module.finrank 𝔽₂ (W ⊔ effectiveRowSpace A : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) : ℝ)⁻¹ := by
    simp_rw [hevent]
    rw [effective_marginal, card_eq_two_pow_finrank
      (V := (W ⊔ effectiveRowSpace A : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)))]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hrank := QuotientRank.joined_rank_add_kernel W (relationMap A)
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  change Module.finrank 𝔽₂ (W ⊔ effectiveRowSpace A : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) +
    Module.finrank 𝔽₂ (W.comap (relationMap A)) = Module.finrank 𝔽₂ W + Fintype.card β at hrank
  unfold conditionalAffineMass
  rw [hjoint, oldObservationMass_eq]
  have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) hrank
  simp only [pow_add] at hpow
  field_simp
  nlinarith

theorem conditionalAffineMass_zero_or_pow (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V)
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    conditionalAffineMass W a A b = 0 ∨ conditionalAffineMass W a A b =
      (2 ^ Module.finrank 𝔽₂ (W.comap (relationMap A)) : ℝ) / (2 ^ Fintype.card β : ℝ) := by
  by_cases h : ∃ w, effectiveEvent W a w ∧ A w = b
  · obtain ⟨w, hw⟩ := h
    exact Or.inr (conditionalAffineMass_of_witness W a A b w hw)
  · left
    unfold conditionalAffineMass finiteExpectation
    have hevent (v : V) : ¬(effectiveEvent W a v ∧ A v = b) := fun hv ↦ h ⟨v, hv⟩
    simp only [ite_eq_right (hevent _), mul_zero, sum_const_zero, zero_div]

theorem conditionalAffineMass_nominal_of_kernel_zero (W : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a : V)
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (hzero : Module.finrank 𝔽₂ (W.comap (relationMap A)) = 0) :
    conditionalAffineMass W a A b = (2 ^ Fintype.card β : ℝ)⁻¹ := by
  let N := W.dualCoannihilator
  let D := A.comp N.subtype
  have hker : LinearMap.ker (relationMap D) = ⊥ := by
    apply bot_unique
    intro u hu
    have hrow : relationMap A u ∈ W := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)]
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      exact DFunLike.congr_fun hu (⟨v, hv⟩ : N)
    have hu0 := (Submodule.finrank_eq_zero.mp hzero).le hrow
    exact hu0
  let : Fintype N := Fintype.ofFinite _
  have hmass := uniformSolutionMass_of_injective_relationMap D (LinearMap.ker_eq_bot.mp hker) (b - A a)
  have hmasspos : 0 < uniformSolutionMass D (b - A a) := by
    rw [hmass]
    exact inv_pos.mpr (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (β → 𝔽₂)))
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp ((uniformSolutionMass_pos_iff D (b - A a)).mp hmasspos)
  have hw : effectiveEvent W a (v.val + a) ∧ A (v.val + a) = b := by
    constructor
    · intro s
      have hs := ((Submodule.mem_dualCoannihilator v.val).mp v.property) s.val s.property
      simp only [map_add, hs, zero_add]
    · change A v.val = b - A a at hv
      rw [map_add, hv, sub_add_cancel]
  rw [conditionalAffineMass_of_witness W a A b _ hw, hzero, pow_zero, one_div]

end PaperP1.Affine
