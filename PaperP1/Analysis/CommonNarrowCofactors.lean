module

public import PaperP1.Analysis.CommonIntervalDirichlet
public import PaperP1.Analysis.CommonAllIntervals
public import PaperP1.Analysis.NarrowPrimeBands
public import PaperP1.Analysis.NarrowRamareRectangle

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonNarrowCofactors
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem common_cofactors_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ X : ℕ, N ≤ 2*X →
      ∀ T : ℝ, 1 ≤ T → (ActualEulerBand.frequencyCutoff (2*X) : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ H j : ℕ, ((N : ℝ)+1)*NarrowPrimeBands.anchor H j ≤ (X : ℝ) →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
          ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
            (NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ))) τ‖ ≤ ε := by
  obtain ⟨R,hR,N₀,hN₀,hs⟩ := CommonAllIntervals.common_all_intervals_small ε δ hε hδ
  refine ⟨R,hR,N₀,hN₀,?_⟩
  intro N hN X hNX T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs N hN (2*X) hNX T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro H j hanchor P hP Q hQ f hf τ hτ hnot
  have hXp : 0 < X := by omega
  have hu := NarrowPrimeBands.anchor_pos H j
  have hu1 := NarrowPrimeBands.anchor_one_le H j
  have hXNN : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  let L := ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊
  let M := ⌈2*(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊
  have hNL : N < L := by
    have hh : (N : ℝ)+1 ≤ (X : ℝ)/NarrowPrimeBands.anchor H j := (le_div_iff₀ hu).mpr hanchor
    have hh' := hh.trans (Nat.le_ceil ((X : ℝ)/NarrowPrimeBands.anchor H j))
    have hNL' : N+1 ≤ L := by exact_mod_cast hh'
    omega
  have hLX : L ≤ X := Nat.ceil_le.mpr ((div_le_iff₀ hu).mpr (by nlinarith only [hu1,hXNN]))
  obtain ⟨_hL,hLM,hML⟩ := NarrowRamareRectangle.cofactor_endpoints X H j hXp
  have hh := hoff L M hNL hLM hML (by omega) P hP Q hQ f hf τ hτ hnot
  rw [NarrowRamareRectangle.cofactorSet_eq_interval X H j hXp]
  exact hh
end PaperP1.CommonNarrowCofactors
