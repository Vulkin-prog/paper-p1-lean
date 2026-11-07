module

public import PaperP1.Asymptotics.SharpExpandedAsymmetricProfile
public import PaperP1.Asymptotics.PrescribedQuadraticKernelTheorem


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RevisedCompanionStatements
open Finset PaperP1 PaperP1.Model
open scoped Classical

theorem companion_T1_10 (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (D Dcut : ℕ)
    (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (2*D+1)*(L+1) ≤ H → H ≤ Dcut*(L+1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x,
        |(n : ℤ)-x| ≤ ((D*(L+1) : ℕ) : ℤ)) →
      ExpandedAsymmetricCoarseProfile.profile N Q L H D old ≤ (N : ℝ)^(31/24+ε) :=
  SharpExpandedAsymmetricProfile.uniform_profile Q hQ C ε D Dcut hD hε

theorem small_prime_bits_unchanged (H z L : ℕ) (U P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ H) :
    AsymmetricEvenLoss.loss H (U ∪ P) z L = AsymmetricEvenLoss.loss H U z L := by
  have hSpace : AsymmetricEvenLoss.oldSpace H (U ∪ P) = AsymmetricEvenLoss.oldSpace H U := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨n,hn,rfl⟩
      rcases Finset.mem_union.mp hn with hU | hp
      · exact AsymmetricEvenLoss.old_mem hU
      · change AsymmetricEvenLoss.largeParity H n ∈ AsymmetricEvenLoss.oldSpace H U
        rw [AsymmetricEvenLoss.largeParity_prime_zero (hP n hp).1 (hP n hp).2]
        exact Submodule.zero_mem _
    · apply Submodule.span_mono
      rintro v ⟨n,hn,rfl⟩
      exact ⟨n,Finset.mem_union_left _ hn,rfl⟩
  exact congrArg (fun S : Submodule Arithmetic.F₂ (ℕ →₀ Arithmetic.F₂) ↦
    Module.finrank Arithmetic.F₂
      (Submodule.comap (EvenImage.evenMap (AsymmetricEvenLoss.newData H z L)) S)) hSpace

theorem companion_T5_1 (D A ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ,
      0 < h → 0 < e → (h : ℝ) ≤ D*(Real.log N)^A →
      ((PrescribedQuadraticKernelTheorem.values N h e β).card : ℝ) ≤
        (N : ℝ)^(QuadraticKernelExponents.exponent β (Real.log e/Real.log N)+ε) ∧
      ((PrescribedQuadraticKernelTheorem.values N h e β).card : ℝ) ≤
        (N : ℝ)^(QuadraticKernelExponents.capped β (Real.log e/Real.log N)+ε) ∧
      ((PrescribedQuadraticKernelTheorem.values N h e β).card : ℝ) ≤
        (N : ℝ)^(QuadraticKernelExponents.affine β (Real.log e/Real.log N)+ε) :=
  PrescribedQuadraticKernelTheorem.actual_exponent_counts D A ε hε

theorem companion_T5_1_exact_comparison (β δ : ℝ) :
    QuadraticKernelExponents.capped β δ ≤ 1/2+β/4-δ/2 :=
  QuadraticKernelExponents.capped_le_affine β δ

end PaperP1.RevisedCompanionStatements
