module

public import PaperP1.Diophantine.GraphPlaneCoarsePointCount
public import PaperP1.Arithmetic.P3GraphPlaneBadSectionCount

/-! # The exact surface point bound derived from actual good-section estimates and proved exceptional-plane counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphPlaneAverageUpperBound

open MvPolynomial Finset GraphPlanePointCounts P3GraphPlaneSection P3GraphPlaneBadSectionCount
open scoped Classical

theorem average_bound {F : Type} [Field F] [Fintype F]
    (P : MvPolynomial (Fin 4) F) (d D : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ a ∈ goodSections P, ((affineZeros (planeSection a P)).card : ℝ) ≤ B)
    (hbad : ∀ a ∈ badSections P,
      ((affineZeros (planeSection a P)).card : ℝ) ≤ (d : ℝ) * Fintype.card F)
    (hbadcard : (badSections P).card ≤ D * Fintype.card F ^ 2) :
    ((affineZeros P).card : ℝ) ≤ (Fintype.card F : ℝ) * B + (D : ℝ) * d * Fintype.card F := by
  classical
  have hm : (∑ a : Fin 3 → F, ((affineZeros (planeSection a P)).card : ℝ)) =
      ((affineZeros P).card : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
    exact_mod_cast GraphPlanePointCounts.first_moment P
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin 3 → F))
    (fun a ↦ Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P)))
    (fun a ↦ ((affineZeros (planeSection a P)).card : ℝ))
  change (∑ a ∈ goodSections P, ((affineZeros (planeSection a P)).card : ℝ)) +
    (∑ a ∈ badSections P, ((affineZeros (planeSection a P)).card : ℝ)) = _ at hsplit
  have hgNat : (goodSections P).card ≤ Fintype.card F ^ 3 := by
    simpa only [goodSections, card_univ, Fintype.card_fun, Fintype.card_fin] using
      (card_le_card (Finset.filter_subset
        (fun a ↦ Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P))) univ))
  have hgR : ((goodSections P).card : ℝ) ≤ (Fintype.card F : ℝ) ^ 3 := by exact_mod_cast hgNat
  have hbR : ((badSections P).card : ℝ) ≤ (D : ℝ) * (Fintype.card F : ℝ) ^ 2 := by
    exact_mod_cast hbadcard
  have hsg : (∑ a ∈ goodSections P, ((affineZeros (planeSection a P)).card : ℝ)) ≤
      (Fintype.card F : ℝ) ^ 3 * B := by
    calc
      _ ≤ ∑ a ∈ goodSections P, B := sum_le_sum hgood
      _ = ((goodSections P).card : ℝ) * B := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hgR hB
  have hsb : (∑ a ∈ badSections P, ((affineZeros (planeSection a P)).card : ℝ)) ≤
      (D : ℝ) * (Fintype.card F : ℝ) ^ 2 * ((d : ℝ) * Fintype.card F) := by
    calc
      _ ≤ ∑ a ∈ badSections P, (d : ℝ) * Fintype.card F := sum_le_sum hbad
      _ = ((badSections P).card : ℝ) * ((d : ℝ) * Fintype.card F) := by
        simp only [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hbR (by positivity)
  have hh : ((affineZeros P).card : ℝ) * (Fintype.card F : ℝ) ^ 2 ≤
      (Fintype.card F : ℝ) ^ 3 * B +
        (D : ℝ) * (Fintype.card F : ℝ) ^ 2 * ((d : ℝ) * Fintype.card F) := by
    linarith
  have he : (Fintype.card F : ℝ) ^ 3 * B +
      (D : ℝ) * (Fintype.card F : ℝ) ^ 2 * ((d : ℝ) * Fintype.card F) =
      ((Fintype.card F : ℝ) * B + (D : ℝ) * d * Fintype.card F) * (Fintype.card F : ℝ) ^ 2 := by ring
  rw [he] at hh
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hq)).mp hh

theorem surface_bound {F : Type} [Field F] [Fintype F]
    (P : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 1 < d) (hP : P.IsHomogeneous d)
    (hgeom : Irreducible (map (algebraMap F (AlgebraicClosure F)) P))
    (D : ℕ) (hbadcard : (badSections P).card ≤ D * Fintype.card F ^ 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hgood : ∀ a ∈ goodSections P, ((affineZeros (planeSection a P)).card : ℝ) ≤ B) :
    ((affineZeros P).card : ℝ) ≤ (Fintype.card F : ℝ) * B + (D : ℝ) * d * Fintype.card F := by
  apply average_bound P d D B hB hgood _ hbadcard
  intro a _
  exact_mod_cast GraphPlaneCoarsePointCount.section_card_le P hd hP hgeom a

theorem uniform_surface_bound (d : ℕ) (hd : 1 < d) :
    ∃ N : ℕ, ∀ (F K : Type) [Field F] [Fintype F] [Field K]
      (P : MvPolynomial (Fin 4) F), P.IsHomogeneous d →
      Irreducible (map (algebraMap F (AlgebraicClosure F)) P) →
      ∀ (φ : F →+* K) (a : Fin 3 → K),
      Irreducible (map (algebraMap K (AlgebraicClosure K)) (planeSection a (map φ P))) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ b ∈ goodSections P, ((affineZeros (planeSection b P)).card : ℝ) ≤ B) →
      ((affineZeros P).card : ℝ) ≤ (Fintype.card F : ℝ) * B + ((d * N : ℕ) : ℝ) * d * Fintype.card F := by
  obtain ⟨N, hN⟩ := uniform_bad_section_bound d
  refine ⟨N, ?_⟩
  intro F K _ _ _ P hP hgeom φ a hgood B hB hcurve
  exact surface_bound P hd hP hgeom (d * N) (hN F K P hP φ a hgood) B hB hcurve

end PaperP1.GraphPlaneAverageUpperBound
