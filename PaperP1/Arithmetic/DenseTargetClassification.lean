module

public import PaperP1.Arithmetic.SelectedTargetClasses
public import PaperP1.Arithmetic.CodedClassTargets

/-! # Actual dense targets admit a strict certificate or a two-class finite code -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTargetClassification

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations PaperP1.PrimeCircuitSupports
  PaperP1.PrimeCircuitGroups PaperP1.PrimeGroupIncidence PaperP1.WindowPrimeIncidence
  PaperP1.ClassPrimeResidual PaperP1.DisjointRecoveryTheorem PaperP1.SelectedTargetClasses

local instance denseTargetClassificationTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance denseTargetClassificationDecEq (W : Type*) : DecidableEq W := Classical.decEq _

def residualExponent (s t k : ℕ) : ℝ :=
  (((t - 1) * PhysicalLabelSupportCount.supportBound s t (t - 1) : ℕ) : ℝ) / k

theorem class_equation {s L H t N k : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hXone : ∀ i, 1 ≤ X i) (ht : 2 ≤ t) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    {α : Module.Dual F₂ M} (hα : α ≠ 0)
    (hsmall : ∀ F ∈ incident X M H hXone hH α, (groupValue X M H hXone hH F) ^ k ≤ N) :
    ∃ D ∈ ClassCoefficientValues.values H
      (PhysicalClassData.sourceProduct (fun a ↦ X (some a)) (physicalClass X M α))
      ⌊(N : ℝ) ^ residualExponent s t k⌋₊,
      IsSquare ((D : ℤ) * ∏ u ∈ PhysicalClassData.offsets (physicalClass X M α), ((X none : ℤ) + u)) := by
  let C := physicalClass X M α
  let m := PhysicalClassData.sourceProduct (fun a ↦ X (some a)) C
  let p := PhysicalClassData.targetProduct (X none) C
  have hm : 0 < m := PhysicalClassData.sourceProduct_pos _ (fun a ↦ hX (some a)) C
  have hp : 0 < p := PhysicalClassData.targetProduct_pos _ (hX none) C
  have hold : oldProduct X M α = m := oldProduct_eq X M hXone α
  have hprod : classProduct X M α = m * p := by
    rw [classProduct_eq, hold, targetProduct_eq X M hXone α]
  have hres := residual_real_bound X M hX hH hXone ht hN hk hM hα hsmall
  have he : RelativeSquarefreeParts.residualPart H (m * p) m ≤ ⌊(N : ℝ) ^ residualExponent s t k⌋₊ := by
    rw [hprod, hold] at hres
    exact Nat.le_floor hres
  obtain ⟨D, hD, hsq⟩ := ClassCoefficientValues.integer_square H m p _ hm hp he
  refine ⟨D, hD, ?_⟩
  rwa [PhysicalClassData.targetProduct_cast (X none) (hXone none) C] at hsq

theorem certificate_or_code {s L H t N k : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hXone : ∀ i, 1 ≤ X i) (ht : 2 ≤ t) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    (hz : X none ∈ Ico N (2 * N))
    (hlabels : k + 2 ≤ (DenseTargetRegularization.targetLabels X L M).card) :
    FixedSourceCertificate.HasStrictCertificate (fun a ↦ X (some a)) L k N (X none) ∨
      X none ∈ CodedClassTargets.targets (fun a ↦ X (some a)) L H (t - 1) N
        ⌊(N : ℝ) ^ residualExponent s t k⌋₊ := by
  obtain ⟨A, hA, hAk, _, hcases⟩ :=
    PrimeGroupDichotomy.certificate_or_small_incident_groups X M hXone hH N k
  rcases hcases with hcert | hsmall
  · exact Or.inl hcert
  obtain ⟨α, hα, β, hβ, hαβ, hαA, hβA⟩ := exists_two X M hXone hH A hA hAk hlabels
  have hαne := ((mem_targetLabels X M α).mp hα).1
  have hβne := ((mem_targetLabels X M β).mp hβ).1
  obtain ⟨D, hD, hsqD⟩ := class_equation X M hX hH hXone ht hN hk hM hαne (hsmall α hαA)
  obtain ⟨E, hE, hsqE⟩ := class_equation X M hX hH hXone ht hN hk hM hβne (hsmall β hβA)
  have hCpool := (CodedClassTargets.mem_pool (physicalClass X M α)).mpr (physicalClass_card X M hM hαne)
  have hFpool := (CodedClassTargets.mem_pool (physicalClass X M β)).mpr (physicalClass_card X M hM hβne)
  apply Or.inr
  apply (CodedClassTargets.mem_targets _ _ _ _ _ _ _).mpr
  refine ⟨(physicalClass X M α, D), (CodedClassTargets.mem_equations _ _ _ _ _ _).mpr ⟨hCpool, hD⟩,
    (physicalClass X M β, E), (CodedClassTargets.mem_equations _ _ _ _ _ _).mpr ⟨hFpool, hE⟩, ?_⟩
  apply (CodedClassTargets.mem_pairSolutions _ _).mpr
  exact ⟨⟨target_offsets_nonempty X M hα, target_offsets_nonempty X M hβ,
    PhysicalClassData.offsets_disjoint (physicalClass_disjoint X M hαβ)⟩, hz, hsqD, hsqE⟩

end PaperP1.DenseTargetClassification
