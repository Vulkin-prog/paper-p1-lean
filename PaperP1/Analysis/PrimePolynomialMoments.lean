module

public import PaperP1.Arithmetic.PrimeProductFibres
public import PaperP1.Analysis.FiniteFibreSquareBudget
public import PaperP1.Analysis.DirichletPolynomialMeanValue

/-! # All-order moments and actual large-value measures of finite prime exponential polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimePolynomialMoments
open PaperP1 Finset BoundedProductFibres GaussianExponentialSums LogarithmicPhase
  FiniteFibreSquareBudget PrimeProductFibres
open scoped Classical

theorem coefficient_square_budget (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (c : ℕ → ℂ) :
    (∑ m ∈ (tuples k P).image value,
      ‖aggregate (tuples k P) value (fun x ↦ ∏ i, c (x i)) m‖^2) ≤
      (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k := by
  have hh := aggregate_square_budget (tuples k P) value (fun x ↦ ∏ i, c (x i)) k.factorial
    (fun m hm ↦ fibre_card_le_factorial k P hP m)
  have he : (∑ x ∈ tuples k P, ‖∏ i, c (x i)‖^2) = (∑ p ∈ P, ‖c p‖^2)^k := by
    rw [sum_pow']
    apply sum_congr rfl
    intro x hx
    rw [norm_prod, ← Finset.prod_pow]
  rw [he] at hh
  exact hh

theorem phase_product {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ S, 0 < n i) (t : ℝ) :
    phase (-Real.log ((∏ i ∈ S, n i : ℕ) : ℝ)) t = ∏ i ∈ S, phase (-Real.log (n i : ℝ)) t := by
  induction S using Finset.induction_on with
  | empty => simp [phase_zero]
  | @insert j S hj ih =>
    rw [prod_insert hj, prod_insert hj, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast Nat.ne_of_gt (hn j (mem_insert_self j S)))
        (by exact_mod_cast Nat.ne_of_gt (prod_pos (fun i hi ↦ hn i (mem_insert_of_mem hi)))),
      neg_add, phase_add, ih (fun i hi ↦ hn i (mem_insert_of_mem hi))]

theorem power_expansion (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (c : ℕ → ℂ) (t : ℝ) :
    (polynomial P c (fun p ↦ -Real.log p) t)^k =
      ∑ x ∈ tuples k P, (∏ i, c (x i)) * phase (-Real.log (value x : ℝ)) t := by
  rw [polynomial, sum_pow']
  apply sum_congr rfl
  intro x hx
  rw [prod_mul_distrib, ← phase_product univ x (fun i _ ↦ hP _ (Fintype.mem_piFinset.mp hx i)) t]
  rfl

theorem aggregate_polynomial {α : Type*} (S : Finset α) (f : α → ℕ) (a : α → ℂ) (t : ℝ) :
    (∑ x ∈ S, a x * phase (-Real.log (f x : ℝ)) t) =
      polynomial (S.image f) (aggregate S f a) (fun m ↦ -Real.log m) t := by
  have hmap : Set.MapsTo f S (S.image f) := fun x hx ↦ mem_image_of_mem f hx
  have he := sum_fiberwise_of_maps_to hmap (fun x ↦ a x * phase (-Real.log (f x : ℝ)) t)
  calc
    _ = ∑ m ∈ S.image f, ∑ x ∈ S.filter (fun x ↦ f x=m), a x * phase (-Real.log (f x : ℝ)) t := he.symm
    _ = _ := by
      apply sum_congr rfl
      intro m hm
      rw [aggregate, sum_mul]
      apply sum_congr (by ext x; simp only [mem_filter])
      intro x hx
      rw [(mem_filter.mp hx).2]
theorem high_moment_bound (k Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (c : ℕ → ℂ)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖polynomial P c (fun p ↦ -Real.log p) t‖^(2*k)) ≤
      Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*((Q^k : ℕ) : ℝ)) *
        (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k := by
  let S := (tuples k P).image value
  let b : ℕ → ℂ := aggregate (tuples k P) value (fun x ↦ ∏ i, c (x i))
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ Q^k := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
    constructor
    · exact prod_pos (fun i _ ↦ (hP _ (Fintype.mem_piFinset.mp hx i)).pos)
    · calc
        value x ≤ ∏ _i : Fin k, Q := prod_le_prod (fun i _ ↦ hQ _ (Fintype.mem_piFinset.mp hx i))
        _ = Q^k := by simp
  have hpower (t : ℝ) : (polynomial P c (fun p ↦ -Real.log p) t)^k =
      polynomial S b (fun n ↦ -Real.log n) t := by
    rw [power_expansion k P (fun p hp ↦ (hP p hp).pos) c t]
    exact aggregate_polynomial (tuples k P) value (fun x ↦ ∏ i, c (x i)) t
  have hnorm (t : ℝ) : ‖polynomial P c (fun p ↦ -Real.log p) t‖^(2*k) =
      ‖polynomial S b (fun n ↦ -Real.log n) t‖^2 := by
    rw [Nat.mul_comm 2 k, pow_mul, ← norm_pow, hpower t]
  have hm := DirichletPolynomialMeanValue.logarithmic_interval_bound S b (Q^k) (pow_pos hQ0 k) hS T hT
  have hc := coefficient_square_budget k P hP c
  change (∑ n ∈ S, ‖b n‖^2) ≤ (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k at hc
  have hb := hm.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  calc
    _ = ∫ t in -T..T, ‖polynomial S b (fun n ↦ -Real.log n) t‖^2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hnorm t
    _ ≤ _ := by simpa only [mul_assoc] using hb

theorem large_values_budget (k Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (c : ℕ → ℂ)
    (T V : ℝ) (hT : 0 < T) (hV : 0 < V) :
    V^(2*k) * MeasureTheory.volume.real {t : ℝ | t ∈ Set.Ioc (-T) T ∧
      V ≤ ‖polynomial P c (fun p ↦ -Real.log p) t‖} ≤
      Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*((Q^k : ℕ) : ℝ)) *
        (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k := by
  let μ := MeasureTheory.volume.restrict (Set.Ioc (-T) T)
  let F : ℝ → ℝ := fun t ↦ ‖polynomial P c (fun p ↦ -Real.log p) t‖^(2*k)
  have hc := polynomial_continuous P c (fun p ↦ -Real.log p)
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  have hint : MeasureTheory.Integrable F μ := (hFc.intervalIntegrable (-T) T).1
  have hnonneg : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall (fun _ ↦ pow_nonneg (norm_nonneg _) _)
  have hm := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint (V^(2*k))
  have hlevel : μ.real {t : ℝ | V ≤ ‖polynomial P c (fun p ↦ -Real.log p) t‖} ≤
      μ.real {t : ℝ | V^(2*k) ≤ F t} := by
    apply MeasureTheory.measureReal_mono
    · intro t ht
      exact pow_le_pow_left₀ hV.le ht _
    · dsimp only [μ]
      finiteness
  have hset : MeasureTheory.volume.real {t : ℝ | t ∈ Set.Ioc (-T) T ∧
      V ≤ ‖polynomial P c (fun p ↦ -Real.log p) t‖} =
      μ.real {t : ℝ | V ≤ ‖polynomial P c (fun p ↦ -Real.log p) t‖} := by
    dsimp only [μ]
    rw [MeasureTheory.measureReal_restrict_apply (measurableSet_le measurable_const hc.norm.measurable)]
    congr 1
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm]
  calc
    _ = V^(2*k) * μ.real {t : ℝ | V ≤ ‖polynomial P c (fun p ↦ -Real.log p) t‖} := by rw [hset]
    _ ≤ V^(2*k) * μ.real {t : ℝ | V^(2*k) ≤ F t} := mul_le_mul_of_nonneg_left hlevel (pow_nonneg hV.le _)
    _ ≤ ∫ t : ℝ, F t ∂μ := hm
    _ ≤ _ := by
      change (∫ t : ℝ in Set.Ioc (-T) T, ‖polynomial P c (fun p ↦ -Real.log p) t‖^(2*k)) ≤ _
      rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact high_moment_bound k Q hQ0 P hP hQ c T hT

theorem large_values_measure (k Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (c : ℕ → ℂ)
    (T V : ℝ) (hT : 0 < T) (hV : 0 < V) :
    MeasureTheory.volume.real {t : ℝ | t ∈ Set.Ioc (-T) T ∧
      V ≤ ‖polynomial P c (fun p ↦ -Real.log p) t‖} ≤
      (Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*((Q^k : ℕ) : ℝ)) *
        (k.factorial : ℝ) * (∑ p ∈ P, ‖c p‖^2)^k) / V^(2*k) := by
  apply (le_div_iff₀ (pow_pos hV (2*k))).mpr
  simpa only [mul_comm] using large_values_budget k Q hQ0 P hP hQ c T V hT hV

end PrimePolynomialMoments
