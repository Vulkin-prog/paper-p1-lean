module

public import PaperP1.Diophantine.AffineSmoothClassAuxiliary
public import PaperP1.Diophantine.SmoothClassPointCount

/-! # Actual affine integer point counts on one smooth residue class

The auxiliary equation has strictly smaller outer degree, so the proved
finite plane intersection theorem applies without an additional premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineSmoothClassPointCount

open Polynomial Finset BivariateDegrees RationalBivariateIrreducibility
open AffineMonomialDeterminant

theorem common_points_card (G F : ℤ[X][X]) (hG : Irreducible (rationalize G))
    (hF : F ≠ 0) (hdegree : degreeY F < degreeY G) (S : Finset (ℤ × ℤ))
    (hz : ∀ z ∈ S, G.evalEval z.1 z.2 = 0 ∧ F.evalEval z.1 z.2 = 0) :
    S.card ≤ (degreeX G + degreeY G) * (degreeX F + degreeY F) := by
  classical
  have hnot : ¬rationalize G ∣ rationalize F := by
    intro hd
    have he := Polynomial.natDegree_le_of_dvd hd (SmoothClassPointCount.rationalize_ne_zero F hF)
    rw [RationalizedCriticalPointBound.outer_degree, RationalizedCriticalPointBound.outer_degree] at he
    omega
  let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
  have hf : Function.Injective f := by
    intro z w he
    exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
      (Int.cast_injective (congrArg Prod.snd he))
  have hb := FinitePlaneBezout.common_points_card (rationalize G) (rationalize F) hG hnot
    (S.image f) (by
      intro z hzS
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hzS
      have hGw : (rationalize G).evalEval (w.1 : ℚ) (w.2 : ℚ) = ((G.evalEval w.1 w.2 : ℤ) : ℚ) :=
        Polynomial.map_mapRingHom_evalEval (Int.castRingHom ℚ) G w.1 w.2
      have hFw : (rationalize F).evalEval (w.1 : ℚ) (w.2 : ℚ) = ((F.evalEval w.1 w.2 : ℤ) : ℚ) :=
        Polynomial.map_mapRingHom_evalEval (Int.castRingHom ℚ) F w.1 w.2
      exact ⟨hGw.trans (by rw [(hz w hw).1]; rfl), hFw.trans (by rw [(hz w hw).2]; rfl)⟩)
  calc
    S.card = (S.image f).card := (card_image_of_injective _ hf).symm
    _ ≤ PlaneCurvePointCount.degree (rationalize G) * PlaneCurvePointCount.degree (rationalize F) := hb
    _ ≤ _ := Nat.mul_le_mul (SmoothClassPointCount.degree_rationalize G)
      (SmoothClassPointCount.degree_rationalize F)

theorem smooth_class_card (p : ℕ) (hp : p.Prime) (G : ℤ[X][X])
    (hGirr : Irreducible (rationalize G)) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (A J : ℕ) (hJ : J < degreeY G) (B : ℝ) (hB : 0 ≤ B) (S : Finset (ℤ × ℤ))
    (hx : ∀ z ∈ S, (p : ℤ) ∣ z.1 - a) (hy : ∀ z ∈ S, (p : ℤ) ∣ z.2 - b)
    (hz : ∀ z ∈ S, G.evalEval z.1 z.2 = 0)
    (hxbox : ∀ z ∈ S, |(z.1 : ℝ)| ≤ B) (hybox : ∀ z ∈ S, |(z.2 : ℝ)| ≤ B)
    (hsmall : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2)) :
    S.card ≤ (degreeX G + degreeY G) * (A + J) := by
  obtain ⟨F, hF, hFX, hFY, hzero⟩ := AffineSmoothClassAuxiliary.exists_auxiliary
    p hp G a b hG hder A J B hB S hx hy hz hxbox hybox hsmall
  have hc := common_points_card G F hGirr hF (hFY.trans_lt hJ) S
    (fun z hzS ↦ ⟨hz z hzS, hzero z hzS⟩)
  exact hc.trans (Nat.mul_le_mul_left _ (Nat.add_le_add hFX hFY))

end PaperP1.AffineSmoothClassPointCount
