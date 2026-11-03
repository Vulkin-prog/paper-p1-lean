module

public import PaperP1.Probability.CompletedPositionalLaw

/-! # Completed positional laws are determined by their actual coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCoefficientExpansion

open Finset UniformSpace PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw

variable {ι : Type*}

local instance positionalCoefficientDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem norm_eq_tsum_abs_coeff (ν : Space ι) : ‖ν‖ = ∑' v, |coeff v ν| := by
  apply le_antisymm ?_ (tsum_abs_coeff_le ν)
  by_contra hn
  have hgap : 0 < ‖ν‖ - ∑' v, |coeff v ν| := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨w, hw⟩ := Completion.denseRange_coe.exists_dist_lt ν (by positivity :
    0 < (‖ν‖ - ∑' v, |coeff v ν|) / 4)
  have hcoe : ofFinite w = (w : Space ι) := rfl
  have hdist : ‖ν - ofFinite w‖ < (‖ν‖ - ∑' v, |coeff v ν|) / 4 := by
    rw [hcoe]
    simpa only [dist_eq_norm] using hw
  let s := w.coeff.support
  have hpoint (v : Configuration ι) : |w.coeff v| ≤ |coeff v ν| + |coeff v (ν - ofFinite w)| := by
    rw [map_sub, coeff_ofFinite]
    have hh := abs_sub_le (w.coeff v) (coeff v ν) 0
    simpa only [sub_zero, abs_sub_comm, add_comm] using hh
  have hfirst : (∑ v ∈ s, |coeff v ν|) ≤ ∑' v, |coeff v ν| :=
    (summable_abs_coeff ν).sum_le_tsum s (fun _ _ ↦ abs_nonneg _)
  have hsecond := finite_sum_abs_coeff_le (ν - ofFinite w) s
  have hnormw : ‖ofFinite w‖ ≤ (∑' v, |coeff v ν|) + ‖ν - ofFinite w‖ := by
    rw [norm_ofFinite]
    change (∑ v ∈ s, |w.coeff v|) ≤ _
    have hh := sum_le_sum (fun v (_hv : v ∈ s) ↦ hpoint v)
    rw [sum_add_distrib] at hh
    exact hh.trans (add_le_add hfirst hsecond)
  have htri := norm_add_le (ν - ofFinite w) (ofFinite w)
  rw [sub_add_cancel] at htri
  linarith only [hgap, hdist, hnormw, htri]

theorem ext {ν κ : Space ι} (h : ∀ v, coeff v ν = coeff v κ) : ν = κ := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [norm_eq_tsum_abs_coeff]
  simp only [map_sub, h, sub_self, abs_zero, tsum_zero]

theorem hasSum_coeff_atoms (ν : Space ι) :
    HasSum (fun v ↦ coeff v ν • ofFinite (atom v)) ν := by
  have hnorm : Summable (fun v ↦ ‖coeff v ν • ofFinite (atom v)‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, norm_ofFinite, l1Norm_atom, mul_one] using
      summable_abs_coeff ν
  have hs := hnorm.of_norm
  have he : (∑' v, coeff v ν • ofFinite (atom v)) = ν := by
    apply ext
    intro v
    have hh := hs.hasSum.map (coeff v) (coeff v).continuous
    have ht (w : Configuration ι) : coeff v (coeff w ν • ofFinite (atom w)) =
        if w = v then coeff w ν else 0 := by
      rw [map_smul, coeff_ofFinite]
      simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]
      split_ifs <;> ring
    dsimp only [Function.comp_def] at hh
    simp_rw [ht] at hh
    simpa only [tsum_ite_eq] using hh.tsum_eq.symm
  have hh := hs.hasSum
  rw [he] at hh
  exact hh

end PaperP1.PositionalCoefficientExpansion
