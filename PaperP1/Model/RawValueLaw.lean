module

public import PaperP1.Model.RawValueIndependence
public import PaperP1.Affine.NominalAffineMass

/-! # Exact raw-word masses from their actual unrestricted parity relations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawValueLaw

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine PaperP1.PrivateValueSystem

variable {ι : Type*} [Fintype ι]

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def columnMap (v : ι → ℕ) : (ι → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun i ↦ parityVec (v i))

theorem relation_zero_iff {M : ℕ} (v : ι → ℕ) (hpos : ∀ i, 0 < v i)
    (hcut : ∀ i, v i ≤ M) (u : ι → F₂) :
    relationMap (valueSystem M v) u = 0 ↔ columnMap v u = 0 := by
  constructor
  · intro hu
    exact PaperP1.RawValueIndependence.relation_of_zero_functional v hpos hcut u hu
  · intro hu
    apply LinearMap.ext
    intro ω
    change (∑ i, u i * valueBit ω (v i)) = 0
    simp only [valueBit, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro p _
    have hz := congrArg (fun z : ℕ →₀ F₂ ↦ z p.val.val) hu
    change (∑ i, u i • parityVec (v i)) p.val.val = 0 at hz
    simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul] at hz
    calc
      _ = ω p * (∑ i, u i * parityVec (v i) p.val.val) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hz, mul_zero]

theorem kernel_eq {M : ℕ} (v : ι → ℕ) (hpos : ∀ i, 0 < v i) (hcut : ∀ i, v i ≤ M) :
    LinearMap.ker (relationMap (valueSystem M v)) = LinearMap.ker (columnMap v) := by
  ext u
  exact relation_zero_iff v hpos hcut u

theorem exact_mass {M : ℕ} (v : ι → ℕ) (hpos : ∀ i, 0 < v i) (hcut : ∀ i, v i ≤ M)
    (b : ι → F₂) :
    uniformSolutionMass (valueSystem M v) b = if Compatible (valueSystem M v) b then
      (2 ^ Module.finrank F₂ (LinearMap.ker (columnMap v)) : ℝ) / (2 ^ Fintype.card ι : ℝ) else 0 := by
  rw [PaperP1.NominalAffineMass.exact_formula, kernel_eq v hpos hcut]
  split <;> simp_all

theorem mass_le {M : ℕ} (v : ι → ℕ) (hpos : ∀ i, 0 < v i) (hcut : ∀ i, v i ≤ M)
    (b : ι → F₂) :
    uniformSolutionMass (valueSystem M v) b ≤
      (2 ^ Module.finrank F₂ (LinearMap.ker (columnMap v)) : ℝ) / (2 ^ Fintype.card ι : ℝ) := by
  classical
  rw [exact_mass v hpos hcut b]
  split
  · exact le_rfl
  · positivity

end PaperP1.RawValueLaw
