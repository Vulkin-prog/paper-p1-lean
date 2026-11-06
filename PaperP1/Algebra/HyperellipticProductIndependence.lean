module

public import PaperP1.Algebra.HyperellipticPureFunctions

/-! # True linear independence of the actual product functions from their proved distinct degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticProductIndependence

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree HyperellipticWeightedMonomials
open HyperellipticPureFunctions
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

theorem linearIndependent_of_pure {ι : Type*} (f : F[X]) (hodd : Odd f.natDegree)
    (z : ι → CurveRing f) (hn : ∀ i, z i ≠ 0) (hpure : ∀ i, Pure f (z i))
    (hdegree : Function.Injective (fun i ↦ poleDegree f (z i))) : LinearIndependent F z := by
  rw [linearIndependent_iff']
  intro S c hsum i hi
  by_contra hci
  let T := S.filter (fun j ↦ c j ≠ 0)
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨k, hk, hmax⟩ := T.exists_max_image (fun j ↦ poleDegree f (z j)) hT
  have hkmem : k ∈ S ∧ c k ≠ 0 := by simpa only [T, Finset.mem_filter] using hk
  obtain ⟨ell, hell, hlower⟩ := leading_functional f hodd (z k) (hn k) (hpure k)
  have hcollapse : (∑ j ∈ S, c j * ell (z j)) = c k * ell (z k) := by
    apply Finset.sum_eq_single k
    · intro j hj hjk
      by_cases hcj : c j = 0
      · rw [hcj, zero_mul]
      · have hjT : j ∈ T := Finset.mem_filter.mpr ⟨hj, hcj⟩
        have hle := hmax j hjT
        have hneq : poleDegree f (z j) ≠ poleDegree f (z k) := fun he ↦ hjk (hdegree he)
        have hlt : poleDegree f (z j) < poleDegree f (z k) := by omega
        rw [hlower (z j) (hpure j) hlt, mul_zero]
    · intro hknot
      exact False.elim (hknot hkmem.1)
  have he := congrArg ell hsum
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at he
  rw [hcollapse] at he
  exact mul_ne_zero hkmem.2 hell he

theorem product_family_linearIndependent (f : F[X]) (hodd : Odd f.natDegree)
    (A B p : ℕ) (hA : A < p) :
    LinearIndependent F (fun ij : PaperP1.HyperellipticMonomialIndex.Index f.natDegree A ×
        PaperP1.HyperellipticMonomialIndex.Index f.natDegree B ↦
      vector f (PaperP1.HyperellipticMonomialIndex.embed f.natDegree A ij.1) *
        vector f (PaperP1.HyperellipticMonomialIndex.embed f.natDegree B ij.2) ^ p) := by
  apply linearIndependent_of_pure f hodd
  · intro i
    exact PaperP1.HyperellipticOddDegreeNorm.product_ne_zero f hodd _ _
      (vector_ne_zero f _) (power_ne_zero f hodd _ (vector_ne_zero f _) p)
  · intro i
    exact pure_mul f _ _ (vector_pure f _) (pure_pow f _ (vector_pure f _) p)
  · intro i j he
    apply PaperP1.HyperellipticMonomialIndex.product_weight_injective f.natDegree A B p hodd hA
    change poleDegree f (vector f (PaperP1.HyperellipticMonomialIndex.embed f.natDegree A i.1) *
      vector f (PaperP1.HyperellipticMonomialIndex.embed f.natDegree B i.2) ^ p) =
      poleDegree f (vector f (PaperP1.HyperellipticMonomialIndex.embed f.natDegree A j.1) *
      vector f (PaperP1.HyperellipticMonomialIndex.embed f.natDegree B j.2) ^ p) at he
    simpa only [product_power_degree f hodd] using he


theorem nonzero_linear_combination (f : F[X]) (hodd : Odd f.natDegree)
    (A B p : ℕ) (hA : A < p)
    (c : HyperellipticMonomialIndex.Index f.natDegree A ×
      HyperellipticMonomialIndex.Index f.natDegree B → F) (hc : c ≠ 0) :
    (∑ ij, c ij •
      (vector f (HyperellipticMonomialIndex.embed f.natDegree A ij.1) *
        vector f (HyperellipticMonomialIndex.embed f.natDegree B ij.2) ^ p)) ≠ 0 := by
  intro hz
  apply hc
  funext i
  exact (linearIndependent_iff').mp (product_family_linearIndependent f hodd A B p hA)
    Finset.univ c hz i (Finset.mem_univ i)

end PaperP1.HyperellipticProductIndependence
