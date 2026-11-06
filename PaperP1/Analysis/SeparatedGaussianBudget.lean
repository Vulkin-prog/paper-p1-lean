module

public import PaperP1.Analysis.GaussianFrequencyRowBound
public import PaperP1.Analysis.SeparatedPositiveBudget


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SeparatedGaussianBudget
open Finset Filter PaperP1
open scoped Classical

def constant : ℝ := 1+Real.sqrt (Real.pi/(1/4 : ℝ))

theorem constant_pos : 0 < constant := by
  unfold constant
  positivity

theorem positive_bound {ι : Type*} (S : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ i ∈ S, 1 ≤ δ i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |δ i-δ j|) :
    (∑ i ∈ S, Real.exp (-(δ i)^2/4)) ≤ Real.sqrt (Real.pi/(1/4 : ℝ))/2 := by
  have hFloor : ∀ i ∈ S, 1 ≤ ⌊δ i⌋₊ := by
    intro i hi
    exact (Nat.le_floor_iff (by linarith only [hδ i hi] : 0 ≤ δ i)).mpr
      (by simpa only [Nat.cast_one] using hδ i hi)
  have hInject := SeparatedPositiveBudget.floor_injective S δ (fun i hi ↦ by linarith only [hδ i hi]) hsep
  have hi : Set.InjOn (fun i ↦ ⌊δ i⌋₊-1) (↑S) := by
    intro i hi j hj he
    have hfi := hFloor i hi
    have hfj := hFloor j hj
    change ⌊δ i⌋₊-1=⌊δ j⌋₊-1 at he
    apply hInject hi hj
    change ⌊δ i⌋₊=⌊δ j⌋₊
    omega
  have hSum := (GaussianFrequencyRowBound.gaussian_tail_summable (1/4) (by norm_num)).sum_le_tsum
    (S.image (fun i ↦ ⌊δ i⌋₊-1)) (fun _ _ ↦ (Real.exp_pos _).le)
  rw [sum_image hi] at hSum
  calc
    _ ≤ ∑ i ∈ S, Real.exp (-(1/4 : ℝ)*((⌊δ i⌋₊-1+1 : ℕ) : ℝ)^2) := by
      apply sum_le_sum
      intro i hi
      rw [show ⌊δ i⌋₊-1+1=⌊δ i⌋₊ by have hh := hFloor i hi; omega]
      apply Real.exp_le_exp.mpr
      have hh := pow_le_pow_left₀ (Nat.cast_nonneg ⌊δ i⌋₊)
        (Nat.floor_le (by linarith only [hδ i hi] : 0 ≤ δ i)) 2
      nlinarith only [hh]
    _ ≤ ∑' n : ℕ, Real.exp (-(1/4 : ℝ)*((n+1 : ℕ) : ℝ)^2) := hSum
    _ ≤ _ := GaussianFrequencyRowBound.gaussian_tail_bound (1/4) (by norm_num)

theorem row_bound {ι : Type*} (S : Finset ι) (τ : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i-τ j|) (i : ι) (hi : i ∈ S) :
    (∑ j ∈ S, Real.exp (-(τ i-τ j)^2/4)) ≤ constant := by
  let P := S.filter (fun j ↦ τ i < τ j)
  let M := S.filter (fun j ↦ τ j < τ i)
  have hP := positive_bound P (fun j ↦ τ j-τ i) (by
    intro j hj
    obtain ⟨hjS,hij⟩ := mem_filter.mp hj
    have hh := hsep i hi j hjS (fun he ↦ (ne_of_lt hij) (congrArg τ he))
    rw [abs_sub_comm,abs_of_pos (sub_pos.mpr hij)] at hh
    exact hh) (by
    intro j hj k hk hne
    convert hsep j (mem_filter.mp hj).1 k (mem_filter.mp hk).1 hne using 1
    congr 1
    ring)
  have hM := positive_bound M (fun j ↦ τ i-τ j) (by
    intro j hj
    obtain ⟨hjS,hji⟩ := mem_filter.mp hj
    have hh := hsep i hi j hjS (fun he ↦ (ne_of_lt hji) (congrArg τ he).symm)
    rwa [abs_of_pos (sub_pos.mpr hji)] at hh) (by
    intro j hj k hk hne
    rw [show (τ i-τ j)-(τ i-τ k)=τ k-τ j by ring,abs_sub_comm]
    exact hsep j (mem_filter.mp hj).1 k (mem_filter.mp hk).1 hne)
  have hP' : (∑ j ∈ P, Real.exp (-(τ i-τ j)^2/4)) ≤ Real.sqrt (Real.pi/(1/4 : ℝ))/2 := by
    convert hP using 1
    apply sum_congr rfl
    intro j hj
    congr 1
    ring
  have hSplit : (∑ j ∈ S, Real.exp (-(τ i-τ j)^2/4)) ≤
      (∑ j ∈ S, if j=i then (1 : ℝ) else 0)+
      (∑ j ∈ P, Real.exp (-(τ i-τ j)^2/4))+(∑ j ∈ M, Real.exp (-(τ i-τ j)^2/4)) := by
    dsimp only [P,M]
    rw [sum_filter,sum_filter,← sum_add_distrib,← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    by_cases hEq : j=i
    · subst j
      simp
    · have hNe : τ i ≠ τ j := by
        intro he
        have hh := hsep i hi j hj (Ne.symm hEq)
        rw [he,sub_self,abs_zero] at hh
        linarith only [hh]
      rcases lt_or_gt_of_ne hNe with hij | hji
      · simp only [hEq,hij,not_lt_of_ge hij.le,ite_false,ite_true,zero_add,add_zero,le_refl]
      · simp only [hEq,hji,not_lt_of_ge hji.le,ite_false,ite_true,zero_add,le_refl]
  have hCenter : (∑ j ∈ S, if j=i then (1 : ℝ) else 0)=1 := by simp [hi]
  rw [hCenter] at hSplit
  unfold constant
  linarith only [hSplit,hP',hM]

theorem quadratic_bound {ι : Type*} (S : Finset ι) (τ : ι → ℝ) (a : ι → ℂ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i-τ j|) :
    (∑ i ∈ S, ∑ j ∈ S, ‖a i‖*‖a j‖*Real.exp (-(τ i-τ j)^2/4)) ≤
      constant*∑ i ∈ S, ‖a i‖^2 := by
  have hh := FiniteSymmetricKernelBudget.symmetric_bound S (fun i ↦ ‖a i‖)
    (fun i j ↦ Real.exp (-(τ i-τ j)^2/4)) constant (fun _ _ _ _ ↦ (Real.exp_pos _).le) (by
      intro i hi j hj
      congr 1
      ring) (fun i hi ↦ row_bound S τ hsep i hi)
  convert hh using 1
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring
end PaperP1.SeparatedGaussianBudget
