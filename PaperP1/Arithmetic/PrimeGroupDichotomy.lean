module

public import PaperP1.Arithmetic.PrimeGroupIncidence
public import PaperP1.Arithmetic.FixedSourceCertificate
public import PaperP1.Combinatorics.TopProductSelection

/-! # Actual prime groups give a source certificate or small residual groups -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeGroupDichotomy

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations PaperP1.PrimeCircuitSupports
  PaperP1.PrimeCircuitGroups PaperP1.PrimeGroupIncidence PaperP1.WindowPrimeIncidence

local instance primeGroupDichotomyTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance primeGroupDichotomyDecEq (W : Type*) : DecidableEq W := Classical.decEq _

theorem selected_certificate {s L H N k : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (A : Finset (Finset (Option (Fin s) × Fin (L + 1))))
    (hA : A ⊆ groups X M H hX hH) (hcard : A.card = k)
    (hprod : N < ∏ F ∈ A, groupValue X M H hX hH F) :
    FixedSourceCertificate.HasStrictCertificate (fun a ↦ X (some a)) L k N (X none) := by
  let e : Fin k ≃ A := (Finset.equivFinOfCardEq hcard).symm
  have hdata (i : Fin k) := group_target_source X M hX hH (hA (e i).property)
  choose u hu _hactive _hpool _hunique a v hav using hdata
  let G : Fin k → ℕ := fun i ↦ groupValue X M H hX hH (e i).val
  refine ⟨G, fun i ↦ (u i).val, ?_, fun i ↦ (u i).isLt, ?_, ?_, ?_⟩
  · intro i
    refine ⟨group_gt_one X M hX hH (hA (e i).property), a i, v i, ?_⟩
    have hdvd := group_dvd_vertex X M hX hH (e i).val (hav i)
    simpa only [value, startCompleteVertexLabel_eq_offset (show 0 < X (some (a i)) from hX _)]
      using hdvd
  · intro i j hij
    apply group_coprime X M hX hH
    intro h
    exact hij (e.injective (Subtype.ext h))
  · have heq : (∏ i, G i) = ∏ F ∈ A, groupValue X M H hX hH F := by
      exact (e.prod_comp (fun F : A ↦ groupValue X M H hX hH F.val)).trans (prod_coe_sort A _)
    rwa [heq]
  · intro i
    have hdvd := group_dvd_vertex X M hX hH (e i).val (hu i)
    simpa only [value, startCompleteVertexLabel_eq_offset (show 0 < X none from hX _)] using hdvd

theorem certificate_or_small_incident_groups {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (N k : ℕ) :
    ∃ A ⊆ groups X M H hX hH, A.card ≤ k ∧ (discarded X M A).card ≤ k ∧
      (FixedSourceCertificate.HasStrictCertificate (fun a ↦ X (some a)) L k N (X none) ∨
        ∀ α : Module.Dual F₂ M, α ∉ discarded X M A →
          ∀ F ∈ incident X M H hX hH α, (groupValue X M H hX hH F) ^ k ≤ N) := by
  obtain ⟨A, hA, hcard, hcases⟩ := TopProductSelection.certificate_or_small_groups
    (groups X M H hX hH) (groupValue X M H hX hH) N k
    (fun F hF ↦ (group_gt_one X M hX hH hF).pos)
  refine ⟨A, hA, hcard, (discarded_card X M hX hH A hA).trans hcard, ?_⟩
  rcases hcases with ⟨hcard, hprod⟩ | hsmall
  · exact Or.inl (selected_certificate X M hX hH A hA hcard hprod)
  · exact Or.inr (fun α hα F hF ↦ hsmall F (incident_outside_selected X M hX hH A hα hF))

end PaperP1.PrimeGroupDichotomy
