module

public import PaperP1.Analysis.PrimePolynomialMoments

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimePowerPolynomial
open Finset PaperP1 BoundedProductFibres GaussianExponentialSums PrimePolynomialMoments
open scoped Classical

def layer (k : ℕ) (P : Finset ℕ) : Finset ℕ := (tuples k P).image value

def coefficient (k : ℕ) (P : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  FiniteFibreSquareBudget.aggregate (tuples k P) value (fun x ↦ ∏ i, f (x i)) n

theorem layer_positive (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    ∀ n ∈ layer k P, 0 < n := by
  intro n hn
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
  exact prod_pos (fun i _hi ↦ hP _ (Fintype.mem_piFinset.mp hx i))

theorem layer_bounds (k : ℕ) (P : Finset ℕ) (L U : ℕ) (hP : P ⊆ Icc L U) :
    layer k P ⊆ Icc (L^k) (U^k) := by
  intro n hn
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
  refine mem_Icc.mpr ⟨?_,?_⟩
  · calc
      L^k = ∏ _i : Fin k, L := by simp
      _ ≤ value x := prod_le_prod (fun i _hi ↦ (mem_Icc.mp (hP (Fintype.mem_piFinset.mp hx i))).1)
  · calc
      value x ≤ ∏ _i : Fin k, U := prod_le_prod (fun i _hi ↦ (mem_Icc.mp (hP (Fintype.mem_piFinset.mp hx i))).2)
      _ = U^k := by simp

theorem coefficient_norm_bound (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (n : ℕ) : ‖coefficient k P f n‖ ≤ (k.factorial : ℝ) := by
  have hprod (x : Fin k → ℕ) (hx : x ∈ tuples k P) : ‖∏ i, f (x i)‖ ≤ 1 := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin k, (1 : ℝ) := prod_le_prod₀ (fun i _hi ↦ norm_nonneg _) (fun i _hi ↦ hf _ (Fintype.mem_piFinset.mp hx i))
      _ = _ := by simp
  unfold coefficient FiniteFibreSquareBudget.aggregate
  calc
    _ ≤ ∑ x ∈ (tuples k P).filter (fun x ↦ value x=n), ‖∏ i, f (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ (tuples k P).filter (fun x ↦ value x=n), (1 : ℝ) :=
      sum_le_sum (fun x hx ↦ hprod x (mem_filter.mp hx).1)
    _ = (((tuples k P).filter (fun x ↦ value x=n)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast PrimeProductFibres.fibre_card_le_factorial k P hP n

theorem power_identity (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (f : ℕ → ℂ) (t : ℝ) :
    (DirichletPolynomialMeanValue.value P f t)^k=
      DirichletPolynomialMeanValue.value (layer k P) (coefficient k P f) t := by
  have hag (n : ℕ) : FiniteFibreSquareBudget.aggregate (tuples k P) value (fun x ↦ ∏ i, f (x i)/(x i : ℂ)) n=
      coefficient k P f n/(n : ℂ) := by
    unfold coefficient FiniteFibreSquareBudget.aggregate
    rw [sum_div]
    apply sum_congr rfl
    intro x hx
    dsimp only
    rw [prod_div_distrib]
    have he : (∏ i, (x i : ℂ))=(n : ℂ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast (mem_filter.mp hx).2
    rw [he]
  change (polynomial P (fun p ↦ f p/(p : ℂ)) (fun p ↦ -Real.log p) t)^k=_
  rw [power_expansion k P hP,aggregate_polynomial]
  unfold DirichletPolynomialMeanValue.value polynomial
  apply sum_congr rfl
  intro n hn
  rw [hag]

theorem reciprocal_layer_mass_bound (k : ℕ) (P : Finset ℕ) :
    (∑ n ∈ layer k P, 1/(n : ℝ)) ≤ (∑ p ∈ P, 1/(p : ℝ))^k := by
  have hmap : ∀ x ∈ tuples k P, value x ∈ layer k P := fun x hx ↦ mem_image.mpr ⟨x,hx,rfl⟩
  have he := sum_fiberwise_of_maps_to hmap (fun x ↦ 1/(value x : ℝ))
  calc
    _ ≤ ∑ n ∈ layer k P, ∑ x ∈ (tuples k P).filter (fun x ↦ value x=n), 1/(value x : ℝ) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
      exact single_le_sum (s := (tuples k P).filter (fun y ↦ value y=value x))
        (f := fun y : Fin k → ℕ ↦ 1/(value y : ℝ)) (a := x)
        (fun y hy ↦ by positivity) (mem_filter.mpr ⟨hx,rfl⟩)
    _ = ∑ x ∈ tuples k P, 1/(value x : ℝ) := he
    _ = _ := by
      rw [sum_pow']
      apply sum_congr rfl
      intro x hx
      change 1/((∏ i, x i : ℕ) : ℝ)=∏ i, (1/(x i : ℝ))
      rw [prod_div_distrib]
      simp only [prod_const_one,Nat.cast_prod]
end PaperP1.PrimePowerPolynomial
