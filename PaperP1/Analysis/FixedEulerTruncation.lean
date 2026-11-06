module

public import PaperP1.Analysis.FinitePrimeDirichletTruncation
public import PaperP1.Analysis.FiniteGaussianPerron
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedEulerTruncation
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def support (P : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  (FinitePrimeDirichletTruncation.indices P Y).image (fun n : Nat.factoredNumbers P ↦ (n : ℕ))

theorem mem_support (P : Finset ℕ) (Y n : ℕ) :
    n ∈ support P Y ↔ 1 ≤ n ∧ n ≤ Y ∧ n ∈ Nat.factoredNumbers P := by
  simp only [support,mem_image,FinitePrimeDirichletTruncation.indices,mem_subtype,mem_Icc]
  constructor
  · rintro ⟨m,hm,rfl⟩
    exact ⟨hm.1,hm.2,m.property⟩
  · rintro ⟨h1,hY,hm⟩
    exact ⟨⟨n,hm⟩,⟨h1,hY⟩,rfl⟩

theorem support_positive (P : Finset ℕ) (Y : ℕ) (n : ℕ) (hn : n ∈ support P Y) : 0 < n :=
  (mem_support P Y n).mp hn |>.1

theorem polynomial_eq_truncated (P : Finset ℕ) (Y : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    FiniteGaussianPerron.polynomial (support P Y) a id t=FinitePrimeDirichletTruncation.truncated P Y a t := by
  unfold FiniteGaussianPerron.polynomial support FinitePrimeDirichletTruncation.truncated
  rw [sum_image]
  · rfl
  · intro m hm n hn he
    exact Subtype.ext he

def primes (X : ℕ) : Finset ℕ := (Icc 1 X).filter Nat.Prime

theorem primes_prime (X p : ℕ) (hp : p ∈ primes X) : p.Prime := (mem_filter.mp hp).2

theorem small_factored (X n : ℕ) (hn : n ∈ Icc 1 X) : n ∈ Nat.factoredNumbers (primes X) := by
  apply Nat.mem_factoredNumbers_iff_forall_le.mpr
  refine ⟨by have hh := (mem_Icc.mp hn).1; omega,?_⟩
  intro p hp hprime _hdiv
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.one_le,hp.trans (mem_Icc.mp hn).2⟩,hprime⟩

theorem support_contains (X Y : ℕ) (hXY : X ≤ Y) : Icc 1 X ⊆ support (primes X) Y := by
  intro n hn
  have h := mem_Icc.mp hn
  exact (mem_support _ _ _).mpr ⟨h.1,h.2.trans hXY,small_factored X n hn⟩

theorem truncation_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y : ℕ) (hY : 0 < Y)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖FinitePrimeDirichletTruncation.total P a t-FiniteGaussianPerron.polynomial (support P Y) a id t‖ ≤
      (1/Real.sqrt (Y : ℝ))*FinitePrimeReciprocalTail.rootEuler P := by
  rw [polynomial_eq_truncated]
  exact (FinitePrimeDirichletTruncation.truncation_error P hP Y a ha t).trans
    (FinitePrimeReciprocalTail.tail_bound P hP (Y : ℝ) (by exact_mod_cast hY))

theorem truncation_small_uniform (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y ≥ Y₀, ∀ a : ℕ → ℂ,
      (∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) → ∀ t : ℝ,
      ‖FinitePrimeDirichletTruncation.total P a t-FiniteGaussianPerron.polynomial (support P Y) a id t‖ ≤ ε := by
  have hs : Tendsto (fun Y : ℕ ↦ Real.sqrt (Y : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun Y : ℕ ↦ (1/Real.sqrt (Y : ℝ))*FinitePrimeReciprocalTail.rootEuler P) atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_const_nhds.div_atTop hs).mul_const (FinitePrimeReciprocalTail.rootEuler P)
  obtain ⟨Y₀,hY₀⟩ := eventually_atTop.mp (hc.eventually (eventually_lt_nhds hε))
  refine ⟨max Y₀ 1,le_max_right _ _,?_⟩
  intro Y hY a ha t
  have hpos : 0 < Y := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hY)
  exact (truncation_bound P hP Y hpos a ha t).trans (hY₀ Y ((le_max_left _ _).trans hY)).le



def majorant (P : Finset ℕ) : ℝ := ∑' n : Nat.factoredNumbers P, 1/(n : ℝ)

theorem majorant_nonneg (P : Finset ℕ) : 0 ≤ majorant P :=
  tsum_nonneg (fun n ↦ by positivity)

theorem total_norm_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖FinitePrimeDirichletTruncation.total P a t‖ ≤ majorant P := by
  have hs := FinitePrimeDirichletTruncation.norm_summable P hP a ha t
  calc
    _ ≤ ∑' n : Nat.factoredNumbers P, ‖DirichletRamareApproximation.twist a n t‖ := norm_tsum_le_tsum_norm hs
    _ ≤ _ := hs.tsum_le_tsum (fun n ↦ by
      rw [DirichletRamareApproximation.twist_norm]
      exact div_le_div_of_nonneg_right (ha n n.property) (Nat.cast_nonneg (n : ℕ)))
      (FinitePrimeDirichletTruncation.reciprocal_summable P hP)

theorem polynomial_norm_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Y : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖FiniteGaussianPerron.polynomial (support P Y) a id t‖ ≤ majorant P := by
  rw [polynomial_eq_truncated]
  calc
    _ ≤ ∑ n ∈ FinitePrimeDirichletTruncation.indices P Y, ‖DirichletRamareApproximation.twist a n t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ FinitePrimeDirichletTruncation.indices P Y, 1/(n : ℝ) := sum_le_sum (fun n _ ↦ by
      rw [DirichletRamareApproximation.twist_norm]
      exact div_le_div_of_nonneg_right (ha n n.property) (Nat.cast_nonneg (n : ℕ)))
    _ ≤ _ := (FinitePrimeDirichletTruncation.reciprocal_summable P hP).sum_le_tsum _ (fun n _ ↦ by positivity)

theorem total_continuous (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) :
    Continuous (FinitePrimeDirichletTruncation.total P a) := by
  change Continuous (fun t : ℝ ↦ ∑' n : Nat.factoredNumbers P, DirichletRamareApproximation.twist a n t)
  apply continuous_tsum (fun n : Nat.factoredNumbers P ↦ DirichletRamareApproximation.twist_continuous a n)
    (FinitePrimeDirichletTruncation.reciprocal_summable P hP)
  intro n t
  rw [DirichletRamareApproximation.twist_norm]
  exact div_le_div_of_nonneg_right (ha n n.property) (Nat.cast_nonneg (n : ℕ))


theorem polynomial_tendsto (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) (t : ℝ) :
    Tendsto (fun Y : ℕ ↦ FiniteGaussianPerron.polynomial (support P Y) a id t) atTop
      (nhds (FinitePrimeDirichletTruncation.total P a t)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨Y₀,_hY₀,hh⟩ := truncation_small_uniform P hP (ε/2) (by positivity)
  refine ⟨Y₀,?_⟩
  intro Y hY
  have he := (hh Y hY a ha t).trans_lt (half_lt_self hε)
  simpa only [dist_eq_norm,norm_sub_rev] using he
end PaperP1.FixedEulerTruncation
