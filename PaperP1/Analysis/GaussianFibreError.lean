module

public import PaperP1.Analysis.FiniteGaussianPerron
public import PaperP1.Analysis.LogarithmicGaussianSum
public import PaperP1.Analysis.TripleCoefficientFibre
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianFibreError
open Finset Nat MeasureTheory PaperP1 FiniteGaussianPerron
open scoped Classical

theorem weighted_fibre_sum_bound {ι : Type*} (E : Finset ι) (a : ι → ℂ) (n : ι → ℕ)
    (A : ℝ) (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hmass : ∀ m : ℕ, (∑ i ∈ E.filter (fun i ↦ n i=m), ‖a i‖) ≤ A*(Real.log (m : ℝ))^2) :
    (∑ i ∈ E, ‖a i‖*w (n i)) ≤ A*(∑ m ∈ E.image n, (Real.log (m : ℝ))^2*w m) := by
  have hf := sum_fiberwise_of_maps_to (s := E) (t := E.image n) (g := n)
    (fun i hi ↦ mem_image_of_mem n hi) (fun i ↦ ‖a i‖*w (n i))
  have he : (∑ i ∈ E, ‖a i‖*w (n i))=
      ∑ m ∈ E.image n, (∑ i ∈ E.filter (fun i ↦ n i=m), ‖a i‖)*w m := by
    rw [← hf]
    apply sum_congr rfl
    intro m hm
    rw [sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [(mem_filter.mp hi).2]
  rw [he]
  calc
    _ ≤ ∑ m ∈ E.image n, (A*(Real.log (m : ℝ))^2)*w m :=
      sum_le_sum (fun m hm ↦ mul_le_mul_of_nonneg_right (hmass m) (hw m))
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro m hm; ring

theorem gaussian_fibre_sum_bound {ι : Type*} (E : Finset ι) (a : ι → ℂ) (n : ι → ℕ)
    (A X δ : ℝ) (hA : 0 ≤ A) (hX : 0 < X) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hn : ∀ i ∈ E, 0 < n i)
    (hmass : ∀ m : ℕ, (∑ i ∈ E.filter (fun i ↦ n i=m), ‖a i‖) ≤ A*(Real.log (m : ℝ))^2) :
    (∑ i ∈ E, ‖a i‖*Real.exp (-(Real.log (X/(n i : ℝ)))^2/(32*δ^2))) ≤
      A*(512*LogarithmicGaussianSum.constant*((Real.log X)^2+1)*(δ*X+1)) := by
  have hh := weighted_fibre_sum_bound E a n A
    (fun m ↦ Real.exp (-(Real.log (X/(m : ℝ)))^2/(32*δ^2))) (fun m ↦ (Real.exp_pos _).le) hmass
  have hb := LogarithmicGaussianSum.finite_reciprocal_weighted_sum (E.image n) X δ hX hδ hδhalf (by
    intro m hm
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
    exact hn i hi)
  exact hh.trans (mul_le_mul_of_nonneg_left hb hA)

theorem sharp_fibre_sum_bound {ι : Type*} (E : Finset ι) (a : ι → ℂ) (n : ι → ℕ)
    (A : ℝ) (hA : 0 ≤ A) (X : ℕ) (hn : ∀ i ∈ E, 0 < n i)
    (hmass : ∀ m : ℕ, (∑ i ∈ E.filter (fun i ↦ n i=m), ‖a i‖) ≤ A*(Real.log (m : ℝ))^2) :
    (∑ i ∈ E.filter (fun i ↦ n i ≤ X), ‖a i‖) ≤ A*((X : ℝ)*(Real.log (X : ℝ))^2) := by
  let w : ℕ → ℝ := fun m ↦ if m ≤ X then 1 else 0
  have hh := weighted_fibre_sum_bound E a n A w (fun m ↦ by dsimp only [w]; split_ifs <;> norm_num) hmass
  have hl : (∑ i ∈ E.filter (fun i ↦ n i ≤ X), ‖a i‖)=∑ i ∈ E, ‖a i‖*w (n i) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i hi
    by_cases hc : n i ≤ X <;> simp only [w,hc,ite_true,ite_false,mul_one,mul_zero]
  have hr : (∑ m ∈ E.image n, (Real.log (m : ℝ))^2*w m)=
      ∑ m ∈ (E.image n).filter (fun m ↦ m ≤ X), (Real.log (m : ℝ))^2 := by
    rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    by_cases hc : m ≤ X <;> simp only [w,hc,ite_true,ite_false,mul_one,mul_zero]
  have hsub : (E.image n).filter (fun m ↦ m ≤ X) ⊆ Icc 1 X := by
    intro m hm
    have hm' := mem_filter.mp hm
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hm'.1
    exact mem_Icc.mpr ⟨hn i hi,hm'.2⟩
  have hb : (∑ m ∈ (E.image n).filter (fun m ↦ m ≤ X), (Real.log (m : ℝ))^2) ≤
      (X : ℝ)*(Real.log (X : ℝ))^2 := by
    calc
      _ ≤ ∑ m ∈ Icc 1 X, (Real.log (m : ℝ))^2 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ sq_nonneg _)
      _ ≤ ∑ m ∈ Icc 1 X, (Real.log (X : ℝ))^2 := by
        apply sum_le_sum
        intro m hm
        apply pow_le_pow_left₀ (Real.log_natCast_nonneg m) _ 2
        exact Real.log_le_log (by exact_mod_cast (mem_Icc.mp hm).1) (by exact_mod_cast (mem_Icc.mp hm).2)
      _ = _ := by simp [Nat.card_Icc]
  rw [hl]
  exact hh.trans (by rw [hr]; exact mul_le_mul_of_nonneg_left hb hA)

def errorBound (A : ℝ) (X : ℕ) (δ : ℝ) : ℝ :=
  A*((Real.exp (δ^2)-1)*(X : ℝ)*(Real.log (X : ℝ))^2+
    2*Real.exp (δ^2)*512*LogarithmicGaussianSum.constant*((Real.log (X : ℝ))^2+1)*(δ*(X : ℝ)+1))

theorem finite_error_bound {ι : Type*} (E : Finset ι) (a : ι → ℂ) (n : ι → ℕ)
    (A : ℝ) (hA : 0 ≤ A) (X : ℕ) (hX : 1 ≤ X) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hn : ∀ i ∈ E, 0 < n i)
    (hmass : ∀ m : ℕ, (∑ i ∈ E.filter (fun i ↦ n i=m), ‖a i‖) ≤ A*(Real.log (m : ℝ))^2) :
    ‖smoothed (δ^2) (X : ℝ) E a n-sharp (X : ℝ) E a n‖ ≤ errorBound A X δ := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hδ1 : δ ≤ 1 := by linarith
  have hdsq := pow_le_pow_left₀ hδ.le hδ1 2
  norm_num only [one_pow] at hdsq
  have hc := cutoff_error (δ^2) (X : ℝ) (sq_pos_of_pos hδ) hdsq hXpos E a n hn
  have hs : (∑ i ∈ E.filter (fun i ↦ (n i : ℝ) ≤ (X : ℝ)), ‖a i‖) ≤ A*((X : ℝ)*(Real.log (X : ℝ))^2) := by
    simpa only [Nat.cast_le] using sharp_fibre_sum_bound E a n A hA X hn hmass
  have hg := gaussian_fibre_sum_bound E a n A (X : ℝ) δ hA hXpos hδ hδhalf hn hmass
  have he : 0 ≤ Real.exp (δ^2)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (sq_nonneg δ))
  calc
    _ ≤ (Real.exp (δ^2)-1)*(∑ i ∈ E.filter (fun i ↦ (n i : ℝ) ≤ (X : ℝ)), ‖a i‖)+
        2*Real.exp (δ^2)*(∑ i ∈ E, ‖a i‖*Real.exp (-(Real.log ((X : ℝ)/(n i : ℝ)))^2/(32*δ^2))) := hc
    _ ≤ (Real.exp (δ^2)-1)*(A*((X : ℝ)*(Real.log (X : ℝ))^2))+
        2*Real.exp (δ^2)*(A*(512*LogarithmicGaussianSum.constant*((Real.log (X : ℝ))^2+1)*(δ*(X : ℝ)+1))) :=
      add_le_add (mul_le_mul_of_nonneg_left hs he) (mul_le_mul_of_nonneg_left hg (by positivity))
    _ = _ := by dsimp only [errorBound]; ring

theorem errorBound_coarse (A : ℝ) (hA : 0 ≤ A) (X : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) :
    errorBound A X δ ≤ A*(2+2*Real.exp 1*(512*LogarithmicGaussianSum.constant))*
      ((Real.log (X : ℝ))^2+1)*(δ*(X : ℝ)+1) := by
  have hδ1 : δ ≤ 1 := by linarith
  have hdsq : δ^2 ≤ δ := by nlinarith
  have hdsq1 : δ^2 ≤ 1 := hdsq.trans hδ1
  have he := Real.abs_exp_sub_one_le (show |δ^2| ≤ 1 by rwa [abs_of_nonneg (sq_nonneg δ)])
  rw [abs_of_nonneg (sq_nonneg δ)] at he
  have hn : Real.exp (δ^2)-1 ≤ 2*δ := by linarith [le_abs_self (Real.exp (δ^2)-1)]
  have hExp : Real.exp (δ^2) ≤ Real.exp 1 := Real.exp_le_exp.mpr hdsq1
  let B : ℝ := ((Real.log (X : ℝ))^2+1)*(δ*(X : ℝ)+1)
  let K : ℝ := 512*LogarithmicGaussianSum.constant
  have hK : 0 < K := by have hc := LogarithmicGaussianSum.constant_pos; dsimp only [K]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsmall : δ*(X : ℝ)*(Real.log (X : ℝ))^2 ≤ B := by
    dsimp only [B]
    nlinarith [sq_nonneg (Real.log (X : ℝ)),mul_nonneg hδ.le (Nat.cast_nonneg X)]
  have hfirst : (Real.exp (δ^2)-1)*(X : ℝ)*(Real.log (X : ℝ))^2 ≤ 2*B := by
    have hh := mul_le_mul_of_nonneg_right hn (mul_nonneg (Nat.cast_nonneg X) (sq_nonneg (Real.log (X : ℝ))))
    nlinarith
  have hsecond : 2*Real.exp (δ^2)*K*B ≤ 2*Real.exp 1*K*B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hExp (by norm_num)) hK.le) hB
  calc
    _ = A*((Real.exp (δ^2)-1)*(X : ℝ)*(Real.log (X : ℝ))^2+2*Real.exp (δ^2)*K*B) := by
      dsimp only [errorBound,K,B]
      ring
    _ ≤ A*(2*B+2*Real.exp 1*K*B) := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hA
    _ = _ := by dsimp only [K,B]; ring

def comparisonConstant (A : ℝ) : ℝ :=
  A*(2+2*Real.exp 1*(512*LogarithmicGaussianSum.constant))/(512*LogarithmicGaussianSum.constant)

theorem errorBound_small_uniform (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀,
      LogarithmicGaussianSum.width X ≤ 1/2 ∧ errorBound A X (LogarithmicGaussianSum.width X) ≤ ε*(X : ℝ) := by
  have hlim : Filter.Tendsto (fun X : ℕ ↦ comparisonConstant A*LogarithmicGaussianSum.scaledBound X)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using LogarithmicGaussianSum.scaledBound_tendsto.const_mul (comparisonConstant A)
  have hhalf := LogarithmicGaussianSum.width_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨X₀,hX₀⟩ := Filter.eventually_atTop.mp ((hlim.eventually (eventually_lt_nhds hε)).and hhalf)
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hh := hX₀ X ((le_max_left _ _).trans hX)
  refine ⟨hh.2.le,?_⟩
  have he := errorBound_coarse A hA X (LogarithmicGaussianSum.width X) (LogarithmicGaussianSum.width_positive X hX2) hh.2.le
  have hc := LogarithmicGaussianSum.constant_pos
  have heq : A*(2+2*Real.exp 1*(512*LogarithmicGaussianSum.constant))*
      ((Real.log (X : ℝ))^2+1)*(LogarithmicGaussianSum.width X*(X : ℝ)+1)=
      (X : ℝ)*(comparisonConstant A*LogarithmicGaussianSum.scaledBound X) := by
    dsimp only [comparisonConstant,LogarithmicGaussianSum.scaledBound]
    field_simp [hXpos.ne',hc.ne']
  exact he.trans (heq.trans_le (by
    have hsmall := mul_le_mul_of_nonneg_left hh.1.le hXpos.le
    simpa only [mul_comm] using hsmall))



theorem actual_triple_cutoff_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ (f : ℕ → ℂ),
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ P Q S : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X) → (∀ q ∈ Q, q.Prime) → (∀ n ∈ S, 0 < n) →
      ‖smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level-
        sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖ ≤ ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀,hh⟩ := errorBound_small_uniform (1/Real.log 2) (by positivity) ε hε
  refine ⟨X₀,hX₀,?_⟩
  intro X hX f hf P Q S hP hQ hS
  have hX2 := hX₀.trans hX
  have hc := finite_error_bound (TripleCoefficientFibre.triples P Q S)
    (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level (1/Real.log 2) (by positivity)
    X (by omega) (LogarithmicGaussianSum.width X) (LogarithmicGaussianSum.width_positive X hX2)
    (hh X hX).1 (TripleCoefficientFibre.level_pos P Q S (fun p hp ↦ (hP p hp).1) hQ hS)
    (TripleCoefficientFibre.actual_coefficient_fibre_bound f hf X P Q S hP hQ hS)
  exact hc.trans (hh X hX).2

theorem actual_finite_triple_perron (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ (f : ℕ → ℂ),
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ P Q S : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X) → (∀ q ∈ Q, q.Prime) → (∀ n ∈ S, 0 < n) →
      ‖sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖ ≤
        ((X : ℝ)/(2*Real.pi))*(∫ t : ℝ,
          Real.exp (-((LogarithmicGaussianSum.width X)^2)*t^2)*
            ‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) t‖*
            ‖WeightedPrimeMean.value Q f t‖*‖polynomial S f id t‖/Real.sqrt (1+t^2))+ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀,hh⟩ := actual_triple_cutoff_small_uniform ε hε
  refine ⟨X₀,hX₀,?_⟩
  intro X hX f hf P Q S hP hQ hS
  have hX2 := hX₀.trans hX
  have hXP : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hδ := LogarithmicGaussianSum.width_positive X hX2
  have he := hh X hX f hf P Q S hP hQ hS
  have hb := smoothed_norm_bound ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (sq_pos_of_pos hδ) hXP
    (TripleCoefficientFibre.triples P Q S) (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level
    (TripleCoefficientFibre.level_pos P Q S (fun p hp ↦ (hP p hp).1) hQ hS)
  have htri : ‖sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S)
      (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖ ≤
      ‖smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
        (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖+ε*(X : ℝ) := by
    calc
      _ = ‖smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level-
        (smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level-
        sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level)‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl he)
  have hr := htri.trans (add_le_add hb le_rfl)
  simpa only [TripleCoefficientFibre.polynomial_factorization f X P Q S (fun p hp ↦ (hP p hp).1) hQ hS,
    norm_mul,mul_assoc] using hr
end PaperP1.GaussianFibreError
