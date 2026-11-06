module

public import PaperP1.Analysis.WeightedDivisorSquare
public import PaperP1.Analysis.PrimePowerPolynomial
public import PaperP1.Analysis.PrimeProductDegree
public import PaperP1.Analysis.PrimeProductDivisorCard
public import PaperP1.Analysis.PrimeProductLcmLayers

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeProductLcmKernel
open Finset PaperP1
open scoped Classical

theorem layers_disjoint (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (j l : ℕ) (hjl : j ≠ l) :
    Disjoint (PrimePowerPolynomial.layer j P) (PrimePowerPolynomial.layer l P) := by
  apply disjoint_left.mpr
  intro n hj hl
  apply hjl
  exact (PrimeProductDegree.degree_of_layer j P hP n hj).symm.trans
    (PrimeProductDegree.degree_of_layer l P hP n hl)

theorem union_mass_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hH : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    (∑ n ∈ (Icc k (2*k)).biUnion (fun j ↦ PrimePowerPolynomial.layer j P), 1/(n : ℝ)) ≤
      ((k+1 : ℕ) : ℝ)*(∑ p ∈ P, 1/(p : ℝ))^k := by
  have hd : Set.PairwiseDisjoint (↑(Icc k (2*k)) : Set ℕ) (fun j ↦ PrimePowerPolynomial.layer j P) := by
    intro j hj l hl hjl
    exact layers_disjoint P hP j l hjl
  rw [sum_biUnion hd]
  have hH0 : (0 : ℝ) ≤ ∑ p ∈ P, 1/(p : ℝ) := sum_nonneg (fun p hp ↦ by positivity)
  have hc : (Icc k (2*k)).card=k+1 := by simp only [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ j ∈ Icc k (2*k), (∑ p ∈ P, 1/(p : ℝ))^j :=
      sum_le_sum (fun j hj ↦ PrimePowerPolynomial.reciprocal_layer_mass_bound j P)
    _ ≤ ∑ _j ∈ Icc k (2*k), (∑ p ∈ P, 1/(p : ℝ))^k :=
      sum_le_sum (fun j hj ↦ pow_le_pow_of_le_one hH0 hH (mem_Icc.mp hj).1)
    _ = _ := by rw [sum_const,nsmul_eq_mul,hc]

theorem kernel_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hH : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    WeightedDivisorSquare.kernel (PrimePowerPolynomial.layer k P) id (fun _ ↦ (1 : ℝ)) ≤
      (16 : ℝ)^k*((k+1 : ℕ) : ℝ)*(∑ p ∈ P, 1/(p : ℝ))^k := by
  let K := PrimePowerPolynomial.layer k P
  let R := K ×ˢ K
  let Z := R.image (fun q ↦ Nat.lcm q.1 q.2)
  have hmap : ∀ q ∈ R, Nat.lcm q.1 q.2 ∈ Z := fun q hq ↦ mem_image.mpr ⟨q,hq,rfl⟩
  have he := sum_fiberwise_of_maps_to hmap (fun q ↦ 1/(Nat.lcm q.1 q.2 : ℝ))
  have hmass : (∑ z ∈ Z, 1/(z : ℝ)) ≤ ((k+1 : ℕ) : ℝ)*(∑ p ∈ P, 1/(p : ℝ))^k := by
    have hs : Z ⊆ (Icc k (2*k)).biUnion (fun j ↦ PrimePowerPolynomial.layer j P) :=
      PrimeProductLcmLayers.image_subset_layers k P hP
    exact (sum_le_sum_of_subset_of_nonneg hs (fun z hz hnot ↦ by positivity)).trans (union_mass_bound k P hP hH)
  calc
    _ = ∑ q ∈ R, 1/(Nat.lcm q.1 q.2 : ℝ) := by
      unfold WeightedDivisorSquare.kernel
      simp only [id,one_mul]
      rw [sum_product]
    _ = ∑ z ∈ Z, ∑ q ∈ R.filter (fun q ↦ Nat.lcm q.1 q.2=z), 1/(Nat.lcm q.1 q.2 : ℝ) := he.symm
    _ ≤ (16 : ℝ)^k*(∑ z ∈ Z, 1/(z : ℝ)) := by
      rw [mul_sum]
      apply sum_le_sum
      intro z hz
      have hc : ((R.filter (fun q ↦ Nat.lcm q.1 q.2=z)).card : ℝ) ≤ (16 : ℝ)^k := by
        exact_mod_cast PrimeProductDivisorCard.lcm_fibre_bound k P hP z hz
      have hconst : (∑ q ∈ R.filter (fun q ↦ Nat.lcm q.1 q.2=z), 1/(Nat.lcm q.1 q.2 : ℝ))=
          ∑ _q ∈ R.filter (fun q ↦ Nat.lcm q.1 q.2=z), 1/(z : ℝ) := by
        apply sum_congr rfl
        intro q hq
        rw [(mem_filter.mp hq).2]
      rw [hconst,sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (16 : ℝ)^k*(((k+1 : ℕ) : ℝ)*(∑ p ∈ P, 1/(p : ℝ))^k) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

theorem constant_weight_kernel (S : Finset ℕ) (c : ℝ) :
    WeightedDivisorSquare.kernel S id (fun _ ↦ c)=c^2*WeightedDivisorSquare.kernel S id (fun _ ↦ (1 : ℝ)) := by
  unfold WeightedDivisorSquare.kernel
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  rw [mul_sum]
  apply sum_congr rfl
  intro b hb
  simp only [id,one_mul]
  ring

theorem factorial_weight_kernel_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hH : (∑ p ∈ P, 1/(p : ℝ)) ≤ 1) :
    WeightedDivisorSquare.kernel (PrimePowerPolynomial.layer k P) id (fun _ ↦ (k.factorial : ℝ)) ≤
      (k.factorial : ℝ)^2*(16 : ℝ)^k*((k+1 : ℕ) : ℝ)*(∑ p ∈ P, 1/(p : ℝ))^k := by
  rw [constant_weight_kernel]
  have hh := mul_le_mul_of_nonneg_left (kernel_bound k P hP hH) (sq_nonneg (k.factorial : ℝ))
  simpa only [mul_assoc] using hh
end PaperP1.PrimeProductLcmKernel
