module

public import PaperP1.Analysis.ValuationDamping
public import PaperP1.Analysis.PrimePowerPolynomial
public import PaperP1.Analysis.PrimeProductDegree

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeProductLcmLayers
open Finset PaperP1
open scoped Classical

theorem multiplicity_lcm_bounds (P : Finset ℕ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    max (ValuationDamping.multiplicity P a) (ValuationDamping.multiplicity P b) ≤
      ValuationDamping.multiplicity P (Nat.lcm a b) ∧
    ValuationDamping.multiplicity P (Nat.lcm a b) ≤
      ValuationDamping.multiplicity P a+ValuationDamping.multiplicity P b := by
  have he : ValuationDamping.multiplicity P (Nat.lcm a b)=
      ∑ p ∈ P, max (a.factorization p) (b.factorization p) := by
    simp only [ValuationDamping.multiplicity,Nat.factorization_lcm ha.ne' hb.ne',Finsupp.sup_apply]
  rw [he]
  constructor
  · apply max_le_iff.mpr
    exact ⟨sum_le_sum (fun p hp ↦ le_max_left _ _),sum_le_sum (fun p hp ↦ le_max_right _ _)⟩
  · rw [ValuationDamping.multiplicity,ValuationDamping.multiplicity,← sum_add_distrib]
    exact sum_le_sum (fun p hp ↦ max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))

theorem supported_lcm (P : Finset ℕ) (a b : ℕ)
    (ha : PrimeProductDegree.supported P a) (hb : PrimeProductDegree.supported P b) :
    PrimeProductDegree.supported P (Nat.lcm a b) := by
  intro p hp hpl
  have hm : p ∣ a*b := dvd_trans hpl (Nat.lcm_dvd_mul a b)
  rcases hp.dvd_mul.mp hm with hpa | hpb
  · exact ha p hp hpa
  · exact hb p hp hpb

theorem lcm_in_layers (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℕ)
    (ha : a ∈ PrimePowerPolynomial.layer k P) (hb : b ∈ PrimePowerPolynomial.layer k P) :
    ∃ j ∈ Icc k (2*k), Nat.lcm a b ∈ PrimePowerPolynomial.layer j P := by
  have ha0 := PrimePowerPolynomial.layer_positive k P (fun p hp ↦ (hP p hp).pos) a ha
  have hb0 := PrimePowerPolynomial.layer_positive k P (fun p hp ↦ (hP p hp).pos) b hb
  have hdeg := multiplicity_lcm_bounds P a b ha0 hb0
  rw [PrimeProductDegree.degree_of_layer k P hP a ha,
    PrimeProductDegree.degree_of_layer k P hP b hb,max_self] at hdeg
  refine ⟨ValuationDamping.multiplicity P (Nat.lcm a b),mem_Icc.mpr ⟨hdeg.1,by omega⟩,?_⟩
  exact PrimeProductDegree.layer_of_supported P (Nat.lcm a b) (Nat.lcm_pos ha0 hb0)
    (supported_lcm P a b (PrimeProductDegree.supported_of_layer k P hP a ha)
      (PrimeProductDegree.supported_of_layer k P hP b hb))

theorem image_subset_layers (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((PrimePowerPolynomial.layer k P ×ˢ PrimePowerPolynomial.layer k P).image
      (fun z ↦ Nat.lcm z.1 z.2)) ⊆
      (Icc k (2*k)).biUnion (fun j ↦ PrimePowerPolynomial.layer j P) := by
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  obtain ⟨j,hj,hn⟩ := lcm_in_layers k P hP z.1 z.2 (mem_product.mp hz).1 (mem_product.mp hz).2
  exact mem_biUnion.mpr ⟨j,hj,hn⟩
end PaperP1.PrimeProductLcmLayers
