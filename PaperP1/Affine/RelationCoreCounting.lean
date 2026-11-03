module

public import PaperP1.Affine.RelationProjectionRank
public import PaperP1.Affine.FullSupportCounting

/-! # Full-support relation mass from lower bounds on actual projection ranks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationCoreCounting

open Finset PaperP1.Affine PaperP1.RelationProjectionRank

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem full_support_lower (I : Finset κ) (k : ℕ) (hcore : ∀ i ∈ I, k ≤ loss S I i) :
    (1 - (I.card : ℝ) / (2 ^ k : ℝ)) * (2 ^ relativeNullityOn S I : ℝ) ≤
      (fullSupportRelations (fun i : I ↦ S i.val)).card := by
  classical
  have hsmall (i : I) : (2 ^ relativeNullityOn S (I.erase i.val) : ℝ) ≤
      (2 ^ relativeNullityOn S I : ℝ) / (2 ^ k : ℝ) := by
    have hdrop := erase_add_loss S I i.val
    have hloss := hcore i.val i.property
    have hnat : relativeNullityOn S (I.erase i.val) + k ≤ relativeNullityOn S I := by omega
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mpr
    simpa only [pow_add] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnat
  have hsum : (∑ i : I, (2 ^ relativeNullityOn S (I.erase i.val) : ℝ)) ≤
      (I.card : ℝ) * ((2 ^ relativeNullityOn S I : ℝ) / (2 ^ k : ℝ)) := by
    calc
      _ ≤ ∑ _i : I, (2 ^ relativeNullityOn S I : ℝ) / (2 ^ k : ℝ) :=
        sum_le_sum (fun i _ ↦ hsmall i)
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hfull : (2 ^ relativeNullityOn S I : ℝ) ≤
      (fullSupportRelations (fun i : I ↦ S i.val)).card +
        ∑ i : I, (2 ^ relativeNullityOn S (I.erase i.val) : ℝ) := by
    exact_mod_cast fullSupport_card_lower S I
  have hid : (1 - (I.card : ℝ) / (2 ^ k : ℝ)) * (2 ^ relativeNullityOn S I : ℝ) =
      (2 ^ relativeNullityOn S I : ℝ) -
        (I.card : ℝ) * ((2 ^ relativeNullityOn S I : ℝ) / (2 ^ k : ℝ)) := by ring
  rw [hid]
  linarith only [hfull, hsum]

theorem half_full_support (I : Finset κ) (hsize : I.card ≤ 256)
    (hcore : ∀ i ∈ I, 9 ≤ loss S I i) :
    (2 ^ relativeNullityOn S I : ℝ) ≤
      2 * (fullSupportRelations (fun i : I ↦ S i.val)).card := by
  have h := full_support_lower S I 9 hcore
  have hsizeR : (I.card : ℝ) ≤ 256 := by exact_mod_cast hsize
  have hcoef : (1 / 2 : ℝ) ≤ 1 - (I.card : ℝ) / (2 ^ 9 : ℝ) := by norm_num; linarith
  have hhalf := (mul_le_mul_of_nonneg_right hcoef
    (by positivity : (0 : ℝ) ≤ 2 ^ relativeNullityOn S I)).trans h
  linarith only [hhalf]

end PaperP1.RelationCoreCounting
