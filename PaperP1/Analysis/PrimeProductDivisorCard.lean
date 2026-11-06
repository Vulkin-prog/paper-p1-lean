module

public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Analysis.ValuationDamping
public import PaperP1.Analysis.PrimePowerPolynomial
public import PaperP1.Analysis.PrimeProductDegree
public import PaperP1.Analysis.PrimeProductLcmLayers

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimeProductDivisorCard
open Finset PaperP1
open scoped Classical

theorem successor_le_two_pow (e : ℕ) : e+1 ≤ (2 : ℕ)^e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    rw [pow_succ]
    have hp : 0 < (2 : ℕ)^e := by positivity
    omega

theorem card_divisors_le_two_pow (P : Finset ℕ) (n : ℕ) (hn : 0 < n)
    (hs : PrimeProductDegree.supported P n) :
    n.divisors.card ≤ 2^(ValuationDamping.multiplicity P n) := by
  have hsub : n.primeFactors ⊆ P := fun p hp ↦ hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  rw [Nat.card_divisors hn.ne']
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (2 : ℕ)^(n.factorization p) :=
      prod_le_prod (fun p hp ↦ successor_le_two_pow (n.factorization p))
    _ = 2^(∑ p ∈ n.primeFactors, n.factorization p) := prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num)
      (sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot ↦ Nat.zero_le _))

theorem pair_fibre_le_divisors_square (A B : Finset ℕ) (z : ℕ) (hz : 0 < z) :
    ((A ×ˢ B).filter (fun q ↦ Nat.lcm q.1 q.2=z)).card ≤ z.divisors.card^2 := by
  have hs : (A ×ˢ B).filter (fun q ↦ Nat.lcm q.1 q.2=z) ⊆ z.divisors ×ˢ z.divisors := by
    intro q hq
    have he := (mem_filter.mp hq).2
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_left q.1 q.2,hz.ne'⟩,
      Nat.mem_divisors.mpr ⟨he ▸ Nat.dvd_lcm_right q.1 q.2,hz.ne'⟩⟩
  simpa only [card_product,pow_two] using card_le_card hs

theorem lcm_fibre_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℕ)
    (hz : z ∈ (PrimePowerPolynomial.layer k P ×ˢ PrimePowerPolynomial.layer k P).image
      (fun q ↦ Nat.lcm q.1 q.2)) :
    ((PrimePowerPolynomial.layer k P ×ˢ PrimePowerPolynomial.layer k P).filter
      (fun q ↦ Nat.lcm q.1 q.2=z)).card ≤ (16 : ℕ)^k := by
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
  obtain ⟨j,hj,hzj⟩ := PrimeProductLcmLayers.lcm_in_layers k P hP q.1 q.2
    (mem_product.mp hq).1 (mem_product.mp hq).2
  have hz0 := PrimePowerPolynomial.layer_positive j P (fun p hp ↦ (hP p hp).pos) _ hzj
  have hs := PrimeProductDegree.supported_of_layer j P hP _ hzj
  have hdeg : ValuationDamping.multiplicity P (Nat.lcm q.1 q.2) ≤ 2*k := by
    rw [PrimeProductDegree.degree_of_layer j P hP _ hzj]
    exact (mem_Icc.mp hj).2
  have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdeg
  calc
    _ ≤ (Nat.lcm q.1 q.2).divisors.card^2 := pair_fibre_le_divisors_square _ _ _ hz0
    _ ≤ (2^(ValuationDamping.multiplicity P (Nat.lcm q.1 q.2)))^2 :=
      Nat.pow_le_pow_left (card_divisors_le_two_pow P _ hz0 hs) 2
    _ ≤ ((2 : ℕ)^(2*k))^2 := Nat.pow_le_pow_left hp 2
    _ = (16 : ℕ)^k := by
      rw [← pow_mul,show (2*k)*2=4*k by ring,pow_mul]
      norm_num
end PaperP1.PrimeProductDivisorCard
