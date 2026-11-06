module

public import PaperP1.Algebra.P3FactorSegreRelations
public import PaperP1.Algebra.P3MultiplicationBaseLocus
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Operations

/-! # Literal prime-ideal and radical consequences of the universal multiplication base-locus computation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorSegrePrimeLocus

open MvPolynomial P3HomogeneousCoefficientFamily P3CoefficientMultiplication P3FactorSegreRelations
open scoped Classical

theorem hom_coefficient {F : Type*} [Field F] (e f : ℕ) (φ : Ring e f →+* F)
    (m : Index (e + f)) :
    φ (coefficientForm e f m) = eval (fun ij ↦ φ (X ij)) (map (Int.castRingHom F) (coefficientForm e f m)) := by
  rw [evaluate_form]
  simp only [coefficientForm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem hom_rank_one {F : Type*} [Field F] (e f : ℕ) (φ : Ring e f →+* F)
    (hI : ideal e f ≤ RingHom.ker φ) :
    ∀ (i k : Index e) (j l : Index f),
      φ (X (i, j)) * φ (X (k, l)) = φ (X (i, l)) * φ (X (k, j)) := by
  intro i k j l
  have hh := RingHom.mem_ker.mp (hI (relation_mem e f i k j l))
  simpa only [relation, map_sub, map_mul, sub_eq_zero] using hh

theorem coordinate_mem_of_coefficients (e f : ℕ) (J : Ideal (Ring e f)) (hJ : J.IsPrime)
    (hI : ideal e f ≤ J) (hcoeff : ∀ m : Index (e + f), coefficientForm e f m ∈ J)
    (ij : Coords e f) : X ij ∈ J := by
  let : J.IsPrime := hJ
  let D := Ring e f ⧸ J
  let F := FractionRing D
  let φ : Ring e f →+* F := (algebraMap D F).comp (Ideal.Quotient.mk J)
  have hkill (P : Ring e f) (hP : P ∈ J) : φ P = 0 := by
    change algebraMap D F (Ideal.Quotient.mk J P) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP, map_zero]
  have hIker : ideal e f ≤ RingHom.ker φ := by
    intro P hP
    exact RingHom.mem_ker.mpr (hkill P (hI hP))
  by_contra hn
  have hpivot : φ (X ij) ≠ 0 := by
    intro hz
    apply hn
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective D F) (hz.trans (map_zero _).symm)
  have hz : (fun kl : Coords e f ↦ φ (X kl)) ≠ 0 := by
    intro hh
    exact hpivot (congrFun hh ij)
  obtain ⟨m, hm⟩ := P3MultiplicationBaseLocus.exists_nonzero_coefficient e f
    (fun kl ↦ φ (X kl)) hz (hom_rank_one e f φ hIker)
  apply hm
  rw [← hom_coefficient e f φ m]
  exact hkill _ (hcoeff m)

def productIdeal (e f : ℕ) : Ideal (Ring e f) :=
  ideal e f ⊔ Ideal.span (Set.range (coefficientForm e f))

theorem variables_le_radical (e f : ℕ) :
    Ideal.span (Set.range (X : Coords e f → Ring e f)) ≤ (productIdeal e f).radical := by
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  intro J hJ
  apply Ideal.span_le.mpr
  rintro _ ⟨ij, rfl⟩
  apply coordinate_mem_of_coefficients e f J hJ.2
  · exact le_trans le_sup_left hJ.1
  · intro m
    apply hJ.1
    exact (le_sup_right : Ideal.span (Set.range (coefficientForm e f)) ≤ productIdeal e f)
      (Ideal.subset_span ⟨m, rfl⟩)

theorem coordinate_mem_radical (e f : ℕ) (ij : Coords e f) :
    X ij ∈ (productIdeal e f).radical :=
  variables_le_radical e f (Ideal.subset_span ⟨ij, rfl⟩)

end PaperP1.P3FactorSegrePrimeLocus
