module

public import PaperP1.Affine.Characters
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The exact positive character density of an old subspace -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectionDensity

open Finset PaperP1.Affine PaperP1.Algebra PaperP1.Probability

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]

def phi (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (x : V) : ℝ :=
  ∑ u : S, realCharacter u.val x

theorem phi_eq (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (x : V) :
    phi S x = if effectiveEvent S 0 x then (Fintype.card S : ℝ) else 0 := by
  have h := effective_character_sum S 0 x
  simpa only [realCharacter, map_zero, binarySign_zero, Int.cast_one, one_mul, phi] using h

theorem phi_nonneg (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (x : V) : 0 ≤ phi S x := by
  rw [phi_eq]
  split_ifs <;> positivity

theorem phi_le_card (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (x : V) :
    phi S x ≤ Fintype.card S := by
  rw [phi_eq]
  split_ifs
  · exact le_rfl
  · positivity

theorem mean_phi [Fintype V] (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] :
    finiteExpectation (uniformFiniteProbability V).weight (phi S) = 1 := by
  classical
  unfold phi
  rw [finiteExpectation_sum]
  simp_rw [uniform_character_expectation]
  have hz : ∀ u : S, u.val = 0 ↔ u = 0 := by
    intro u
    constructor
    · exact fun h ↦ Subtype.ext h
    · rintro rfl
      rfl
  simp_rw [hz]
  simp

theorem phi_rpow (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (p : ℝ) (hp : 0 < p) (x : V) :
    (phi S x) ^ p = (Fintype.card S : ℝ) ^ (p - 1) * phi S x := by
  have hc : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  rw [phi_eq]
  split_ifs
  · calc
      (Fintype.card S : ℝ) ^ p = (Fintype.card S : ℝ) ^ ((p - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hc, Real.rpow_one]
  · simp only [Real.zero_rpow hp.ne', mul_zero]

theorem mean_phi_rpow [Fintype V] (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (p : ℝ) (hp : 0 < p) :
    finiteExpectation (uniformFiniteProbability V).weight (fun x ↦ (phi S x) ^ p) =
      (Fintype.card S : ℝ) ^ (p - 1) := by
  simp_rw [phi_rpow S p hp]
  rw [finiteExpectation_const_mul, mean_phi, mul_one]

theorem mean_phi_rpow_root [Fintype V] (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (p : ℝ) (hp : 0 < p) :
    (finiteExpectation (uniformFiniteProbability V).weight (fun x ↦ (phi S x) ^ p)) ^ (1 / p) =
      (Fintype.card S : ℝ) ^ (1 - 1 / p) := by
  rw [mean_phi_rpow S p hp, ← Real.rpow_mul (by positivity)]
  congr 1
  field_simp

theorem mean_phi_character [Fintype V] (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S]
    (u : V →ₗ[𝔽₂] 𝔽₂) :
    finiteExpectation (uniformFiniteProbability V).weight (fun x ↦ phi S x * realCharacter u x) =
      if u ∈ S then 1 else 0 := by
  classical
  have hprod : (fun x ↦ phi S x * realCharacter u x) =
      (fun x ↦ ∑ s : S, realCharacter (s.val + u) x) := by
    funext x
    unfold phi
    simp_rw [sum_mul, realCharacter_add]
  rw [hprod, finiteExpectation_sum]
  simp_rw [uniform_character_expectation]
  by_cases hu : u ∈ S
  · let s₀ : S := ⟨-u, S.neg_mem hu⟩
    have heq : ∀ s : S, s.val + u = 0 ↔ s = s₀ := by
      intro s
      rw [add_eq_zero_iff_eq_neg]
      constructor
      · exact fun h ↦ Subtype.ext h
      · rintro rfl
        rfl
    simp_rw [heq]
    simp [hu]
  · have hne : ∀ s : S, s.val + u ≠ 0 := by
      intro s hz
      have heq : u = -s.val := (eq_neg_iff_add_eq_zero).mpr (by simpa only [add_comm] using hz)
      exact hu (heq ▸ S.neg_mem s.property)
    simp [hne, hu]

end PaperP1.ProjectionDensity
