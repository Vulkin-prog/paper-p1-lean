module

public import PaperP1.Geometry.FiniteSurfaceCurveHilbert
public import PaperP1.Geometry.GradedProjectiveCurveData
public import PaperP1.Algebra.FiniteComponentHilbertBudget
public import PaperP1.Algebra.RegularSurfaceHilbertSection
public import PaperP1.Algebra.HomogeneousPrincipalComponents

/-! # Actual surface section components retain the total curve-degree budget on every normalized chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedSurfaceSectionCurveBudget

open Polynomial

theorem exists_family {F A : Type*} [Field F] [Infinite F] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra F A] (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (MvPolynomial.aeval (R := F) g).Finite)
    (hinj : Function.Injective (MvPolynomial.aeval (R := F) g))
    (p : ℚ[X]) (hpdeg : p.natDegree ≤ 2) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H p)
    (d : ℕ) (hcoeff : p.coeff 2 = (d : ℚ) / 2)
    (e : ℕ) (f : A) (hf : f ∈ H e) (hf0 : f ≠ 0) (b : A) (hb : b ∈ H 1) :
    ∃ family : Finset (GradedProjectiveCurveData.Curve H),
      family.card ≤ e * d ∧ (∀ Γ ∈ family, f ∈ Γ.ideal ∧ Γ.degree ≤ ((e * d : ℕ) : ℚ)) ∧
      (∑ Γ ∈ family, Γ.degree) ≤ ((e * d : ℕ) : ℚ) ∧
      ∀ φ : A →ₐ[F] F, φ f = 0 → φ b ≠ 0 → ∃ Γ ∈ family, Γ.ideal ≤ RingHom.ker φ.toRingHom := by
  classical
  have hcomponents := HomogeneousPrincipalComponents.finite_cover H hf hf0
  let T := (HomogeneousPrincipalComponents.components f).filter fun P ↦ b ∉ P
  have hminimal (P : T) : P.val ∈ (Ideal.span {f}).minimalPrimes :=
    (HomogeneousPrincipalComponents.mem_components f P.val).mp (Finset.mem_filter.mp P.property).1
  have hprime (P : T) : P.val.IsPrime := (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).1
  have hhom (P : T) : P.val.IsHomogeneous H := (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).2.1
  have hheight (P : T) : P.val.height = 1 := (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).2.2.1
  have hcurve (P : T) : ∃ (r : ℕ) (β : ℚ), 0 < r ∧ GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece H P.val) (C (r : ℚ) * X + C β) := by
    let := hprime P
    exact FiniteSurfaceCurveHilbert.exists_nat_linear_hilbert H g hg hfinite hinj P.val (hhom P) (hheight P)
  choose degree β hdegree hhilbert using hcurve
  let make (P : T) : GradedProjectiveCurveData.Curve H := {
    point := {
      asHomogeneousIdeal := ⟨P.val, hhom P⟩
      isPrime := hprime P
      not_irrelevant_le := by
        intro hle
        exact (Finset.mem_filter.mp P.property).2
          (hle (HomogeneousIdeal.mem_irrelevant_of_mem H (by decide : 0 < 1) hb)) }
    height := hheight P
    degree := (degree P : ℚ)
    degree_pos := Nat.cast_pos.mpr (hdegree P)
    constant := β P
    hilbert := hhilbert P }
  have hinc (P Q : T) (hne : Q ≠ P) : ¬ Q.val ≤ P.val := by
    intro hle
    have he : P.val = Q.val := le_antisymm ((hminimal P).2 ⟨hprime Q, (hminimal Q).le⟩ hle) hle
    exact hne (Subtype.ext he.symm)
  have hsection := RegularSurfaceHilbertSection.linear_hilbert H p hpdeg hp d hcoeff hf
    (fun a a' he ↦ mul_right_cancel₀ hf0 he)
  have hsum : (∑ P : T, (degree P : ℚ)) ≤ ((e * d : ℕ) : ℚ) :=
    FiniteComponentHilbertBudget.sum_linear_degree_le H (Ideal.span {f}) (fun P : T ↦ P.val)
      hprime hhom hinc (fun P ↦ (hminimal P).le) ((e * d : ℕ) : ℚ)
      ((e : ℚ) * p.coeff 1 - (e : ℚ) ^ 2 * p.coeff 2) (fun P ↦ (degree P : ℚ)) β hsection hhilbert
  have hTcard : T.card ≤ e * d := by
    have hcard : (T.card : ℚ) ≤ ∑ P : T, (degree P : ℚ) := by
      calc
        (T.card : ℚ) = ∑ _P : T, (1 : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun P _ ↦ by exact_mod_cast (hdegree P : 1 ≤ degree P))
    exact_mod_cast hcard.trans hsum
  have hbound (P : T) : (degree P : ℚ) ≤ ((e * d : ℕ) : ℚ) :=
    (Finset.single_le_sum (fun Q _ ↦ Nat.cast_nonneg (degree Q)) (Finset.mem_univ P)).trans hsum
  let family := T.attach.image make
  have hsumFamily : (∑ Γ ∈ family, Γ.degree) ≤ ((e * d : ℕ) : ℚ) := by
    calc
      _ ≤ ∑ P ∈ T.attach, (make P).degree :=
        Finset.sum_image_le_of_nonneg (fun Γ _hΓ ↦ Γ.degree_pos.le)
      _ = ∑ P : T, (degree P : ℚ) := by simp only [Finset.attach_eq_univ, make]
      _ ≤ _ := hsum
  refine ⟨family, Finset.card_image_le.trans (by simpa only [Finset.card_attach] using hTcard), ?_, hsumFamily, ?_⟩
  · intro Γ hΓ
    obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp hΓ
    exact ⟨(hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).2.2.2, hbound P⟩
  · intro φ hφf hφb
    obtain ⟨P, hP, hPQ, hbP⟩ := hcomponents.2 φ b hφf hφb
    have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hP, hbP⟩
    exact ⟨make ⟨P, hPT⟩, Finset.mem_image.mpr ⟨⟨P, hPT⟩, Finset.mem_attach _ _, rfl⟩, hPQ⟩

end PaperP1.GradedSurfaceSectionCurveBudget
