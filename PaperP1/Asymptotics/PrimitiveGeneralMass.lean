module

public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Asymptotics.LargeBoundaryTail

/-! # Elementary fixed-order primitive mass: the exponent 1-r/2 needs no dense certificate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveGeneralMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveWindowMass PaperP1.FamilyIndependentMass

theorem binary_factor {N L : ℕ} {C : ℝ} (hN : 0 < N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 ^ L : ℝ) ≤ (2 : ℝ) ^ C * N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : (L : ℝ) ≤ Real.log N / Real.log 2 + C := by
    have h := (abs_le.mp hband).2
    linarith
  have he : (L : ℝ) * Real.log 2 ≤ Real.log N + C * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_right hupper hlog.le
    rw [add_mul, div_mul_cancel₀ _ hlog.ne'] at h
    exact h
  calc
    (2 ^ L : ℝ) = Real.exp ((L : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (Real.log N + C * Real.log 2) := Real.exp_le_exp.mpr he
    _ = _ := by
      rw [Real.exp_add, Real.exp_log hn, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        mul_comm C (Real.log 2), mul_comm]

theorem uniform_mass (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
        mass (primitiveFamilies G L r) L ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, hNM⟩ := OriginalWindowFamilyMass.article_10_2 r hr C (ε / 2) (by positivity)
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C)
    (1 - (r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NM NF), ?_⟩
  intro N hN L G hband hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm := (hNM N (by omega) L G hband hG).2.2.2
  have hF : ∀ I ∈ primitiveFamilies G L r, I.Nonempty ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x := by
    intro I hI
    obtain ⟨hI, hprim⟩ := mem_filter.mp hI
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hI
    refine ⟨card_pos.mp (by omega), hprim, ?_⟩
    intro x hx
    have hNx := (mem_Ico.mp (hG (hsub hx))).1
    omega
  calc
    _ ≤ (2 ^ L : ℝ) * independentMass (primitiveFamilies G L r) L := primitive_mass_le _ L hF
    _ ≤ (2 ^ L : ℝ) * (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hm (pow_nonneg (by norm_num) _)
    _ ≤ ((2 : ℝ) ^ C * N) * (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right (binary_factor (by omega) hband) (Real.rpow_nonneg hn.le _)
    _ = (2 : ℝ) ^ C * (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2) := by
      conv_rhs =>
        rw [show 1 - (r : ℝ) / 2 + ε / 2 = 1 + (-(r : ℝ) / 2 + ε / 2) by ring,
          Real.rpow_add hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2 + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_submass (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ F : Finset (Finset ℕ),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      F ⊆ primitiveFamilies G L r → mass F L ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  obtain ⟨NM, hNM⟩ := uniform_mass r hr C ε hε
  refine ⟨NM, ?_⟩
  intro N hN L G F hband hG hF
  exact (sum_le_sum_of_subset_of_nonneg hF (fun I _ _ ↦ weight_nonneg L I)).trans
    (hNM N hN L G hband hG)

theorem actual_joint_submass (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ F : Finset (Finset ℕ),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      F ⊆ primitiveFamilies G L r →
        (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  obtain ⟨NM, hNM⟩ := uniform_submass r hr C ε hε
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  refine ⟨max NM NL, ?_⟩
  intro N hN L G F hband hG hF
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  exact (sum_le_sum fun I _ ↦ joint_le_weight L hL I).trans (hNM N (by omega) L G F hband hG hF)

theorem actual_centered_submass (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ F : Finset (Finset ℕ),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      F ⊆ primitiveFamilies G L r → (∀ x ∈ G, 0 < infiniteMarginal x L) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, hNM⟩ := uniform_submass r hr C ε hε
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  refine ⟨max NM NL, ?_⟩
  intro N hN L G F hband hG hF hp
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  apply (le_trans ?_ (hNM N (by omega) L G F hband hG hF))
  apply sum_le_sum
  intro I hI
  obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp (hF hI)).1
  exact centered_le_weight L hL I (card_pos.mp (by omega)) (fun x hx ↦ hp x (hIG hx))

theorem from_four (r : ℕ) (hr : 4 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
        mass (primitiveFamilies G L r) L ≤ (N : ℝ) ^ (-(4 : ℝ) / 5 + ε) := by
  obtain ⟨NM, hNM⟩ := uniform_mass r (by omega) C ε hε
  refine ⟨max 1 NM, ?_⟩
  intro N hN L G hband hG
  apply (hNM N (by omega) L G hband hG).trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

theorem main_15_5_from_five (r : ℕ) (hr : 5 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ F : Finset (Finset ℕ),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      F ⊆ primitiveFamilies G L r →
        mass F L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε) ∧
        mass F L ≤ (N : ℝ) ^ (-(2 * (r : ℝ)) / (r + 2) + ε) := by
  obtain ⟨NM, hNM⟩ := uniform_submass r (by omega) C ε hε
  refine ⟨max 1 NM, ?_⟩
  intro N hN L G F hband hG hF
  have hm := hNM N (by omega) L G F hband hG hF
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have hfirst : 1 - (r : ℝ) / 2 ≤ -(4 : ℝ) / 3 := by linarith
  have hsecond : 1 - (r : ℝ) / 2 ≤ -(2 * (r : ℝ)) / (r + 2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 2)).mpr
    have hprod := mul_nonneg (sub_nonneg.mpr hrR) (by positivity : (0 : ℝ) ≤ (r : ℝ) + 1)
    nlinarith only [hprod]
  exact ⟨hm.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith)),
    hm.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))⟩

end PaperP1.PrimitiveGeneralMass
