module

public import PaperP1.Analysis.PrimePolynomialMoments
public import PaperP1.Analysis.WeightedDivisorSquare

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteDirichletConvolution
open Finset PaperP1 GaussianExponentialSums LogarithmicPhase
open scoped Classical

def support (A B : Finset ℕ) : Finset ℕ := (A ×ˢ B).image (fun z ↦ z.1*z.2)

def coefficient (A B : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ A, if d ∣ n ∧ n/d ∈ B then a d*b (n/d) else 0

theorem coefficient_eq_fibre (A B : Finset ℕ) (hA : ∀ d ∈ A, 0 < d)
    (a b : ℕ → ℂ) (n : ℕ) :
    coefficient A B a b n=∑ z ∈ (A ×ˢ B).filter (fun z ↦ z.1*z.2=n), a z.1*b z.2 := by
  rw [coefficient,← sum_filter]
  symm
  apply sum_bij (fun z _hz ↦ z.1)
  · intro z hz
    obtain ⟨hz,he⟩ := mem_filter.mp hz
    obtain ⟨hd,hm⟩ := mem_product.mp hz
    have hdiv : z.1 ∣ n := he ▸ dvd_mul_right z.1 z.2
    have hquot : n/z.1=z.2 := by rw [← he,Nat.mul_div_cancel_left z.2 (hA z.1 hd)]
    exact mem_filter.mpr ⟨hd,hdiv,hquot ▸ hm⟩
  · intro z hz y hy he
    apply Prod.ext he
    apply Nat.eq_of_mul_eq_mul_left (hA z.1 (mem_product.mp (mem_filter.mp hz).1).1)
    calc
      z.1*z.2=n := (mem_filter.mp hz).2
      _ = z.1*y.2 := by rw [he]; exact (mem_filter.mp hy).2.symm
  · intro d hd
    obtain ⟨hd,hdiv,hm⟩ := mem_filter.mp hd
    exact ⟨(d,n/d),mem_filter.mpr ⟨mem_product.mpr ⟨hd,hm⟩,Nat.mul_div_cancel' hdiv⟩,rfl⟩
  · intro z hz
    have he := (mem_filter.mp hz).2
    have hquot : n/z.1=z.2 := by
      rw [← he,Nat.mul_div_cancel_left z.2 (hA z.1 (mem_product.mp (mem_filter.mp hz).1).1)]
    rw [hquot]

theorem support_positive (A B : Finset ℕ) (hA : ∀ d ∈ A, 0 < d) (hB : ∀ m ∈ B, 0 < m) :
    ∀ n ∈ support A B, 0 < n := by
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  exact Nat.mul_pos (hA z.1 (mem_product.mp hz).1) (hB z.2 (mem_product.mp hz).2)

theorem support_bounds (A B : Finset ℕ) (L₁ U₁ L₂ U₂ : ℕ)
    (hA : A ⊆ Icc L₁ U₁) (hB : B ⊆ Icc L₂ U₂) : support A B ⊆ Icc (L₁*L₂) (U₁*U₂) := by
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  have ha := mem_Icc.mp (hA (mem_product.mp hz).1)
  have hb := mem_Icc.mp (hB (mem_product.mp hz).2)
  exact mem_Icc.mpr ⟨Nat.mul_le_mul ha.1 hb.1,Nat.mul_le_mul ha.2 hb.2⟩

theorem coefficient_norm_bound (A B : Finset ℕ) (a b : ℕ → ℂ) (w : ℕ → ℝ)
    (ha : ∀ d ∈ A, ‖a d‖ ≤ w d) (hb : ∀ m ∈ B, ‖b m‖ ≤ 1) (n : ℕ) :
    ‖coefficient A B a b n‖ ≤ WeightedDivisorSquare.divisorSum A id w n := by
  unfold coefficient WeightedDivisorSquare.divisorSum
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro d hd
  dsimp only [id]
  by_cases ht : d ∣ n ∧ n/d ∈ B
  · rw [ite_eq_left ht,ite_eq_left ht.1,norm_mul]
    exact (mul_le_mul (ha d hd) (hb (n/d) ht.2) (norm_nonneg _) ((norm_nonneg _).trans (ha d hd))).trans_eq (by ring)
  · rw [ite_eq_right ht,norm_zero]
    split_ifs
    · exact (norm_nonneg _).trans (ha d hd)
    · exact le_rfl

theorem product_identity (A B : Finset ℕ) (hA : ∀ d ∈ A, 0 < d) (hB : ∀ m ∈ B, 0 < m)
    (a b : ℕ → ℂ) (t : ℝ) :
    DirichletPolynomialMeanValue.value A a t*DirichletPolynomialMeanValue.value B b t=
      DirichletPolynomialMeanValue.value (support A B) (coefficient A B a b) t := by
  let prod := fun z : ℕ × ℕ ↦ z.1*z.2
  let c := fun z : ℕ × ℕ ↦ a z.1*b z.2/((z.1*z.2 : ℕ) : ℂ)
  have hi : DirichletPolynomialMeanValue.value A a t*DirichletPolynomialMeanValue.value B b t=
      ∑ z ∈ A ×ˢ B, c z*phase (-Real.log (prod z : ℝ)) t := by
    rw [sum_product]
    change (∑ d ∈ A, a d/(d : ℂ)*phase (-Real.log (d : ℝ)) t)*
      (∑ m ∈ B, b m/(m : ℂ)*phase (-Real.log (m : ℝ)) t)=_
    rw [sum_mul]
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro m hm
    dsimp only [c,prod]
    have hphase : phase (-Real.log ((d*m : ℕ) : ℝ)) t=
        phase (-Real.log (d : ℝ)) t*phase (-Real.log (m : ℝ)) t := by
      rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hA d hd).ne') (by exact_mod_cast (hB m hm).ne'),
        neg_add,phase_add]
    rw [hphase,Nat.cast_mul]
    ring
  have hag (n : ℕ) : FiniteFibreSquareBudget.aggregate (A ×ˢ B) prod c n=
      coefficient A B a b n/(n : ℂ) := by
    rw [coefficient_eq_fibre A B hA a b n,sum_div]
    unfold FiniteFibreSquareBudget.aggregate
    apply sum_congr rfl
    intro z hz
    dsimp only [c]
    have he : z.1*z.2=n := (mem_filter.mp hz).2
    rw [he]
  rw [hi,PrimePolynomialMoments.aggregate_polynomial]
  unfold DirichletPolynomialMeanValue.value polynomial
  apply sum_congr rfl
  intro n hn
  rw [hag]
end PaperP1.FiniteDirichletConvolution
