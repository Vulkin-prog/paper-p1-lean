module

public import PaperP1.Diophantine.SmoothClassPointCount
public import PaperP1.Diophantine.FiniteFieldPlaneZeroBound

/-! # Canonical smooth residue classes of the actual signed projective points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothResidueClasses

open Polynomial Finset PaperP1.BidegreeOneFibreCount PaperP1.BivariateDegrees

def badInteger (G : ℤ[X][X]) (z : Point) : ℤ :=
  z.1 1 * z.2 1 * MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
    (IntegerFactorProjectiveCurve.projective G.derivative)

def residue (p : ℕ) (z : Point) : ZMod p × ZMod p :=
  ((z.1 0 : ZMod p) * (z.1 1 : ZMod p)⁻¹, (z.2 0 : ZMod p) * (z.2 1 : ZMod p)⁻¹)

theorem good_data (p : ℕ) (G : ℤ[X][X]) (z : Point) (hgood : ¬(p : ℤ) ∣ badInteger G z) :
    (¬(p : ℤ) ∣ z.1 1) ∧ (¬(p : ℤ) ∣ z.2 1) ∧
      ¬(p : ℤ) ∣ MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
        (IntegerFactorProjectiveCurve.projective G.derivative) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  · intro hd
    exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  · intro hd
    exact hgood (dvd_mul_of_dvd_right hd _)

theorem normalized_zero_iff (p : ℕ) (hp : p.Prime) (F : ℤ[X][X]) (z : Point)
    (hx : ¬(p : ℤ) ∣ z.1 1) (hy : ¬(p : ℤ) ∣ z.2 1) :
    (((MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective F) : ℤ) : ZMod p) = 0) ↔
      BivariateEvaluation.evaluate (residue p z).1 (residue p z).2 F = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hX : (z.1 1 : ZMod p) ≠ 0 := fun h ↦ hx ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hY : (z.2 1 : ZMod p) ≠ 0 := fun h ↦ hy ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  let X : (ZMod p)ˣ := Units.mk0 _ hX
  let Y : (ZMod p)ˣ := Units.mk0 _ hY
  have heX : ![(z.1 0 : ZMod p), (X : ZMod p)] = (fun i ↦ (z.1 i : ZMod p)) := by
    funext i
    fin_cases i <;> rfl
  have heY : ![(z.2 0 : ZMod p), (Y : ZMod p)] = (fun i ↦ (z.2 i : ZMod p)) := by
    funext i
    fin_cases i <;> rfl
  have he := ProjectiveUnitCharts.zero_iff F (z.1 0 : ZMod p) (z.2 0 : ZMod p) X Y
  rw [heX, heY, ProjectiveUnitCharts.integer_cast] at he
  simpa [residue, X, Y] using he

theorem residue_smooth (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (z : Point)
    (hgood : ¬(p : ℤ) ∣ badInteger G z)
    (hcurve : MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0) :
    BivariateEvaluation.evaluate (residue p z).1 (residue p z).2 G = 0 ∧
      BivariateEvaluation.evaluate (residue p z).1 (residue p z).2 G.derivative ≠ 0 := by
  obtain ⟨hx, hy, hd⟩ := good_data p G z hgood
  constructor
  · apply (normalized_zero_iff p hp G z hx hy).mp
    rw [hcurve, Int.cast_zero]
  · intro hz
    have he := (normalized_zero_iff p hp G.derivative z hx hy).mpr hz
    exact hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he)

theorem residue_congruence (p : ℕ) (hp : p.Prime) (x : Fin 2 → ℤ)
    (hx : ¬(p : ℤ) ∣ x 1) (a : ℤ)
    (ha : (a : ZMod p) = (x 0 : ZMod p) * (x 1 : ZMod p)⁻¹) :
    (p : ℤ) ∣ x 0 - a * x 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : (x 1 : ZMod p) ≠ 0 := fun h ↦ hx ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Int.cast_sub, Int.cast_mul]
  rw [ha, mul_assoc, inv_mul_cancel₀ hd, mul_one, sub_self]

theorem classPoint_of_residue (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (z : Point)
    (hgood : ¬(p : ℤ) ∣ badInteger G z)
    (hcurve : MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (a b : ℤ) (ha : (a : ZMod p) = (residue p z).1) (hb : (b : ZMod p) = (residue p z).2) :
    SmoothClassAuxiliary.ClassPoint p G a b z := by
  obtain ⟨hx, hy, _⟩ := good_data p G z hgood
  exact ⟨hx, hy, residue_congruence p hp z.1 hx a ha,
    residue_congruence p hp z.2 hy b hb, hcurve⟩

theorem residue_image_card (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (S : Finset Point)
    (hgood : ∀ z ∈ S, ¬(p : ℤ) ∣ badInteger G z)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0) :
    (S.image (residue p)).card ≤ (degreeX G + degreeY G) * p := by
  apply FiniteFieldPlaneZeroBound.smooth_integer_classes_card p hp G
  intro r hr
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
  exact residue_smooth p hp G z (hgood z hz) (hcurve z hz)

theorem fixed_prime_count (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (H J : ℕ) (hJ : J < degreeY G)
    (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hgood : ∀ z ∈ S, ¬(p : ℤ) ∣ badInteger G z)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L)
    (hy : ∀ z ∈ S, ∀ c, |(z.2 c : ℝ)| ≤ Y)
    (hsmall : ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
      (p : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2)) :
    S.card ≤ 4 * (degreeX G + degreeY G) ^ 2 * (H + J) * p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hf (r : ZMod p × ZMod p) (hr : r ∈ S.image (residue p)) :
      (S.filter (fun z ↦ residue p z = r)).card ≤ 4 * (degreeX G + degreeY G) * (H + J) := by
    obtain ⟨z₀, hz₀, he₀⟩ := mem_image.mp hr
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective r.1
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective r.2
    have hs := residue_smooth p hp G z₀ (hgood z₀ hz₀) (hcurve z₀ hz₀)
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
    apply SmoothClassPointCount.smooth_class_card p hp G hne hgeom a b hbaseZ hderZ H J hJ
      L Y hL hY (S.filter (fun z ↦ residue p z = r))
      (fun z hz ↦ hprim z (mem_filter.mp hz).1)
      (fun z hz ↦ classPoint_of_residue p hp G z (hgood z (mem_filter.mp hz).1)
        (hcurve z (mem_filter.mp hz).1) a b
        (ha.trans (congrArg Prod.fst (mem_filter.mp hz).2).symm)
        (hb.trans (congrArg Prod.snd (mem_filter.mp hz).2).symm))
      (fun z hz c ↦ hx z (mem_filter.mp hz).1 c)
      (fun z hz c ↦ hy z (mem_filter.mp hz).1 c) hsmall
  calc
    S.card = ∑ r ∈ S.image (residue p), (S.filter (fun z ↦ residue p z = r)).card :=
      card_eq_sum_card_image _ _
    _ ≤ ∑ _r ∈ S.image (residue p), 4 * (degreeX G + degreeY G) * (H + J) := sum_le_sum hf
    _ = (S.image (residue p)).card * (4 * (degreeX G + degreeY G) * (H + J)) := by simp
    _ ≤ ((degreeX G + degreeY G) * p) * (4 * (degreeX G + degreeY G) * (H + J)) :=
      Nat.mul_le_mul_right _ (residue_image_card p hp G S hgood hcurve)
    _ = _ := by ring

end PaperP1.SmoothResidueClasses
