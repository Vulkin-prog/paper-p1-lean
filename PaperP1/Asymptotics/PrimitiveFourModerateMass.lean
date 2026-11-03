module

public import PaperP1.Asymptotics.FixedOrderAnchorMass
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The four-anchor moderate part of the primitive four-window rank mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveFourModerateMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrimitiveWindowMass
  PaperP1.ConnectedWindowFamilies PaperP1.FixedOrderAnchorMass

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 4 ∧ Primitive L I ∧
        Covered 4 4 (L + 1) N (PaperP1.MultiAnchorOrder.cutoff 6 N) ((N : ℝ) ^ (9 / 10 : ℝ)) I) →
      mass F L ≤ (N : ℝ) ^ (-(29 : ℝ) / 15 + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := PaperP1.FixedOrderAnchorMass.uniform_bound 4 4 C
    (2 * (2 : ℝ) ^ C) 6 (9 / 10) (ε / 2) (by norm_num) (by norm_num)
    (by positivity) (by norm_num) (by norm_num) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C)
    (-(29 : ℝ) / 15 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NM + NP + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass := hm N (by omega) L hband (fun x ↦ infiniteMarginal x L)
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (hp N (by omega) L hband) F (by
      intro I hI
      exact ⟨(hF I hI).1, (hF I hI).2.1, (hF I hI).2.2.2⟩)
  have hprim : ∀ I ∈ F, I.Nonempty ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x := by
    intro I hI
    refine ⟨card_pos.mp (by rw [(hF I hI).2.1]; omega), (hF I hI).2.2.1, ?_⟩
    intro x hx
    have h := (mem_Ico.mp ((hF I hI).1 hx)).1
    omega
  calc
    _ ≤ (2 ^ L : ℝ) * ∑ I ∈ F, ∏ x ∈ I, infiniteMarginal x L := primitive_mass_le F L hprim
    _ ≤ ((2 : ℝ) ^ C * N) * (N : ℝ) ^ (-(4 : ℝ) * (9 / 10) + 4 / 6 + ε / 2) :=
      mul_le_mul (PrimitiveGeneralMass.binary_factor (by omega) hband) hmass
        (sum_nonneg fun I _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        (by positivity)
    _ = (2 : ℝ) ^ C * (N : ℝ) ^ (-(29 : ℝ) / 15 + ε / 2) := by
      have heq : 1 + (-(4 : ℝ) * (9 / 10) + 4 / 6 + ε / 2) = -(29 : ℝ) / 15 + ε / 2 := by ring
      conv_rhs => rw [← heq, Real.rpow_add hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-(29 : ℝ) / 15 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrimitiveFourModerateMass
