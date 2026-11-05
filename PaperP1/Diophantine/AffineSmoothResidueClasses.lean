module

public import PaperP1.Diophantine.AffineSmoothClassPointCount
public import PaperP1.Arithmetic.CoarseGeometricPlaneCount

/-! # Summing actual affine smooth residue classes with exact monomial weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineSmoothResidueClasses

open Polynomial Finset BivariateDegrees RationalBivariateIrreducibility
open AffineMonomialDeterminant SmoothResidueClasses CoarseGeometricPlaneCount

def affineResidue (p : ℕ) (z : ℤ × ℤ) : ZMod p × ZMod p := residue p (lift z)

theorem residue_image_card (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (S : Finset (ℤ × ℤ))
    (hgood : ∀ z ∈ S, ¬(p : ℤ) ∣ badInteger G (lift z))
    (hcurve : ∀ z ∈ S, G.evalEval z.1 z.2 = 0) :
    (S.image (affineResidue p)).card ≤ (degreeX G + degreeY G) * p := by
  have hc := SmoothResidueClasses.residue_image_card p hp G (S.image lift) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    exact hgood w hw) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    exact lift_curve G w (hcurve w hw))
  change (S.image (fun z ↦ residue p (lift z))).card ≤ _
  simpa only [image_image, Function.comp_def] using hc

theorem fixed_prime_count (p : ℕ) (hp : p.Prime) (G : ℤ[X][X])
    (hGirr : Irreducible (rationalize G)) (A J : ℕ) (hJ : J < degreeY G)
    (B : ℝ) (hB : 0 ≤ B) (S : Finset (ℤ × ℤ))
    (hgood : ∀ z ∈ S, ¬(p : ℤ) ∣ badInteger G (lift z))
    (hcurve : ∀ z ∈ S, G.evalEval z.1 z.2 = 0)
    (hx : ∀ z ∈ S, |(z.1 : ℝ)| ≤ B) (hy : ∀ z ∈ S, |(z.2 : ℝ)| ≤ B)
    (hsmall : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2)) :
    S.card ≤ (degreeX G + degreeY G) ^ 2 * (A + J) * p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hf (r : ZMod p × ZMod p) (hr : r ∈ S.image (affineResidue p)) :
      (S.filter (fun z ↦ affineResidue p z = r)).card ≤ (degreeX G + degreeY G) * (A + J) := by
    obtain ⟨z₀, hz₀, he₀⟩ := mem_image.mp hr
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective r.1
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective r.2
    have hs := residue_smooth p hp G (lift z₀) (hgood z₀ hz₀) (lift_curve G z₀ (hcurve z₀ hz₀))
    have hbase : BivariateEvaluation.evaluate (a : ZMod p) (b : ZMod p) G = 0 := by
      rw [ha, hb, ← he₀]
      exact hs.1
    have hder : BivariateEvaluation.evaluate (a : ZMod p) (b : ZMod p) G.derivative ≠ 0 := by
      rw [ha, hb, ← he₀]
      exact hs.2
    have hbaseZ : (p : ℤ) ∣ G.evalEval a b := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [← BivariateEvaluation.integer_evaluation]
      exact hbase
    have hderZ : ¬(p : ℤ) ∣ G.derivative.evalEval a b := by
      intro hd
      apply hder
      rw [BivariateEvaluation.integer_evaluation]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have hclass (z : ℤ × ℤ) (hz : z ∈ S.filter (fun z ↦ affineResidue p z = r)) :
        SmoothClassAuxiliary.ClassPoint p G a b (lift z) := by
      exact classPoint_of_residue p hp G (lift z) (hgood z (mem_filter.mp hz).1)
        (lift_curve G z (hcurve z (mem_filter.mp hz).1)) a b
        (ha.trans (congrArg Prod.fst (mem_filter.mp hz).2).symm)
        (hb.trans (congrArg Prod.snd (mem_filter.mp hz).2).symm)
    apply AffineSmoothClassPointCount.smooth_class_card p hp G hGirr a b hbaseZ hderZ
      A J hJ B hB (S.filter (fun z ↦ affineResidue p z = r))
    · intro z hz
      simpa [lift] using (hclass z hz).residueX
    · intro z hz
      simpa [lift] using (hclass z hz).residueY
    · intro z hz
      exact hcurve z (mem_filter.mp hz).1
    · intro z hz
      exact hx z (mem_filter.mp hz).1
    · intro z hz
      exact hy z (mem_filter.mp hz).1
    · exact hsmall
  calc
    S.card = ∑ r ∈ S.image (affineResidue p), (S.filter (fun z ↦ affineResidue p z = r)).card :=
      card_eq_sum_card_image _ _
    _ ≤ ∑ _r ∈ S.image (affineResidue p), (degreeX G + degreeY G) * (A + J) := sum_le_sum hf
    _ = (S.image (affineResidue p)).card * ((degreeX G + degreeY G) * (A + J)) := by simp
    _ ≤ ((degreeX G + degreeY G) * p) * ((degreeX G + degreeY G) * (A + J)) :=
      Nat.mul_le_mul_right _ (residue_image_card p hp G S hgood hcurve)
    _ = _ := by ring

end PaperP1.AffineSmoothResidueClasses
