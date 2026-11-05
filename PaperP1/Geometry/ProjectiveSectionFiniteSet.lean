module

public import PaperP1.Geometry.ProjectiveHomogeneousSectionPoints
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # Actual projective-space point sets and their homogeneous section bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveSectionFiniteSet

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

def sectionLocus {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) (f : MvPolynomial σ F) :
    Set (Projectivization F (σ → F)) :=
  {p | (∀ P ∈ I, eval p.rep P = 0) ∧ eval p.rep f = 0}

theorem rep_injective {F σ : Type*} [Field F] :
    Function.Injective (fun p : Projectivization F (σ → F) ↦ p.rep) := by
  intro p q he
  have hh : (⟨p.rep, p.rep_ne_zero⟩ : {w : σ → F // w ≠ 0}) = ⟨q.rep, q.rep_ne_zero⟩ := Subtype.ext he
  have hk := congrArg (Projectivization.mk' F) hh
  simpa only [Projectivization.mk'_eq_mk, Projectivization.mk_rep] using hk

theorem mem_section_mk_iff {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ F)) {e : ℕ}
    (f : MvPolynomial σ F) (hf : f.IsHomogeneous e) (w : σ → F) (hw : w ≠ 0) :
    Projectivization.mk F w hw ∈ sectionLocus I f ↔ (∀ P ∈ I, eval w P = 0) ∧ eval w f = 0 := by
  let p := Projectivization.mk F w hw
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F w hw
  change (fun i ↦ (a : F) * w i) = p.rep at ha
  have hback : (fun i ↦ (a : F)⁻¹ * p.rep i) = w := by
    funext i
    rw [← congrFun ha i, ← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]
  constructor
  · intro hp
    have hpI : ∀ P ∈ I, eval p.rep P = 0 := hp.1
    have hpf : eval p.rep f = 0 := hp.2
    constructor
    · intro P hP
      have hh := HomogeneousIdealPointScaling.zeros_scale I hI p.rep hpI (a : F)⁻¹ P hP
      rwa [hback] at hh
    · have hh : eval (fun i ↦ (a : F)⁻¹ * p.rep i) f = 0 := by
        rw [HomogeneousPolynomialEvaluation.eval_scale f hf, hpf, mul_zero]
      rwa [hback] at hh
  · rintro ⟨hcurve, hsection⟩
    constructor
    · intro P hP
      have hh := HomogeneousIdealPointScaling.zeros_scale I hI w hcurve (a : F) P hP
      rwa [ha] at hh
    · change eval p.rep f = 0
      rw [← ha, HomogeneousPolynomialEvaluation.eval_scale f hf, hsection, mul_zero]

theorem card_bound {F σ : Type*} [Field F] [Infinite F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e) (hnot : f ∉ I)
    (S : Finset (Projectivization F (σ → F))) (hS : ∀ p ∈ S, p ∈ sectionLocus I f) :
    S.card ≤ e * d := by
  classical
  let T := S.image (fun p ↦ p.rep)
  have hcard : T.card = S.card := Finset.card_image_of_injective _ rep_injective
  have hc := ProjectiveHomogeneousSectionPoints.projective_population I hI hprime d hd b₀ hp f hf hnot T (by
    intro w hw
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hw
    exact p.rep_ne_zero) (by
    intro v hv w hw hrel
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨c, _hc, he⟩ := hrel
    have hproj : p = q := by
      have hh := (Projectivization.mk_eq_mk_iff' F p.rep q.rep p.rep_ne_zero q.rep_ne_zero).mpr
        ⟨c, funext (fun i ↦ (he i).symm)⟩
      simpa only [Projectivization.mk_rep] using hh
    exact congrArg (fun r : Projectivization F (σ → F) ↦ r.rep) hproj) (by
    intro w hw P hP
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hw
    exact (hS p hpS).1 P hP) (by
    intro w hw
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hw
    exact (hS p hpS).2)
  rw [hcard] at hc
  exact hc

theorem rational_curve_card {σ : Type} [Finite σ] (Γ : ProjectiveCurveData.Curve σ) {e : ℕ}
    (f : MvPolynomial σ ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal)
    (S : Finset (Projectivization ℚ (σ → ℚ))) (hS : ∀ p ∈ S, p ∈ sectionLocus Γ.ideal f) :
    S.card ≤ e * ProjectiveCurveHilbertDegree.natDegree Γ := by
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial (ProjectiveCurveData.piece Γ.ideal)
      (Polynomial.C (ProjectiveCurveHilbertDegree.natDegree Γ : ℚ) * Polynomial.X + Polynomial.C Γ.constant) := by
    rw [ProjectiveCurveHilbertDegree.natDegree_cast Γ]
    exact Γ.hilbert
  exact card_bound Γ.ideal Γ.homogeneous Γ.prime _ (ProjectiveCurveHilbertDegree.natDegree_pos Γ)
    Γ.constant hp f hf hnot S hS

theorem finite_locus {F σ : Type*} [Field F] [Infinite F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e) (hnot : f ∉ I) :
    (sectionLocus I f).Finite := by
  by_contra hbad
  have hinf : (sectionLocus I f).Infinite := hbad
  obtain ⟨S, hS, hcard⟩ := hinf.exists_subset_card_eq (e * d + 1)
  have hc := card_bound I hI hprime d hd b₀ hp f hf hnot S (fun _ hs ↦ hS hs)
  omega

theorem exists_finset {F σ : Type*} [Field F] [Infinite F] [Finite σ]
    (I : Ideal (MvPolynomial σ F)) (hI : I.IsHomogeneous (homogeneousSubmodule σ F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    {e : ℕ} (f : MvPolynomial σ F) (hf : f.IsHomogeneous e) (hnot : f ∉ I) :
    ∃ E : Finset (Projectivization F (σ → F)),
      (∀ p, p ∈ E ↔ p ∈ sectionLocus I f) ∧ E.card ≤ e * d := by
  classical
  have hfinite := finite_locus I hI hprime d hd b₀ hp f hf hnot
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · exact fun _ ↦ hfinite.mem_toFinset
  · exact card_bound I hI hprime d hd b₀ hp f hf hnot _ (fun _ hp ↦ hfinite.mem_toFinset.mp hp)

end PaperP1.ProjectiveSectionFiniteSet
