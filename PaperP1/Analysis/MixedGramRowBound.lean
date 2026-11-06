module

public import PaperP1.Analysis.SquareRootGramBound
public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.SeparatedAbsoluteBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.MixedGramRowBound
open Finset PaperP1 LogarithmicPhase GaussianExponentialSums FiniteGramLargeValues
open scoped Classical

def rowBudget (N R : ℕ) (A T : ℝ) : ℝ :=
  (N : ℝ)+6*(N : ℝ)*(1+Real.log A)+2*A^2+(R : ℝ)*SquareRootGramBound.cap N A T

theorem rowBudget_nonneg (N R : ℕ) (A T : ℝ) (hA : 1 ≤ A) : 0 ≤ rowBudget N R A T := by
  have hl := Real.log_nonneg hA
  have hc := SquareRootGramBound.cap_nonneg N A T
  unfold rowBudget
  positivity

theorem row_bound {ι : Type*} (R : Finset ι) (τ : ι → ℝ) (T A : ℝ) (hT : 1 ≤ T) (hA : 1 ≤ A)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (r : ι) (hr : r ∈ R) :
    (∑ s ∈ R, ‖gram (Ico N (2*N)) (fun r n ↦ phase (-Real.log n) (τ r)) r s‖) ≤ rowBudget N R.card A T := by
  let S := R.erase r
  let P := S.filter (fun s ↦ |τ s-τ r| ≤ A)
  let M := S.filter (fun s ↦ ¬|τ s-τ r| ≤ A)
  let G := fun s ↦ ‖gram (Ico N (2*N)) (fun r n ↦ phase (-Real.log n) (τ r)) r s‖
  have hPS : P ⊆ R := (filter_subset _ _).trans (erase_subset _ _)
  have hMS : M ⊆ R := (filter_subset _ _).trans (erase_subset _ _)
  have hpδ : ∀ s ∈ P, 1 ≤ |τ s-τ r| ∧ |τ s-τ r| ≤ A := by
    intro s hs
    have hsE := (mem_filter.mp hs).1
    exact ⟨hsep s (mem_erase.mp hsE).2 r hr (mem_erase.mp hsE).1,(mem_filter.mp hs).2⟩
  have hnear := SeparatedAbsoluteBudget.weighted_distance_bound P τ (τ r) A hA hpδ
    (fun s hs u hu hne ↦ hsep s (hPS hs) u (hPS hu) hne) (3*(N : ℝ)) 1 (by positivity) (by norm_num)
  have hpbound : (∑ s ∈ P, G s) ≤ 6*(N : ℝ)*(1+Real.log A)+2*A^2 := by
    calc
      _ ≤ ∑ s ∈ P, (3*(N : ℝ)/|τ s-τ r|+1*|τ s-τ r|) := by
        apply sum_le_sum
        intro s hs
        have hnonzero : τ r-τ s ≠ 0 := by
          have hp := (hpδ s hs).1
          intro he
          have he' : τ s-τ r=0 := by linarith
          rw [he',abs_zero] at hp
          linarith
        have hc := DirichletGramLargeValues.dyadic_correlation N hN τ r s hnonzero
        simpa only [G,abs_sub_comm,one_mul] using hc
      _ ≤ 6*(N : ℝ)*(1+Real.log A)+2*A^2 := by nlinarith only [hnear]
  have hfar : (∑ s ∈ M, G s) ≤ (R.card : ℝ)*SquareRootGramBound.cap N A T := by
    calc
      _ ≤ ∑ _s ∈ M, SquareRootGramBound.cap N A T := by
        apply sum_le_sum
        intro s hs
        have hlow : A ≤ |τ r-τ s| := by
          have hp := (lt_of_not_ge (mem_filter.mp hs).2).le
          simpa only [abs_sub_comm] using hp
        have hupp : |τ r-τ s| ≤ 2*T := by
          apply abs_le.mpr
          constructor <;> linarith [(htau r hr).1,(htau r hr).2,(htau s (hMS hs)).1,(htau s (hMS hs)).2]
        change ‖gram (Ico N (2*N)) (fun r n ↦ phase (-Real.log n) (τ r)) r s‖ ≤ _
        rw [DirichletGramLargeValues.gram_identity]
        exact SquareRootGramBound.actual_sum_bound N hN (τ r-τ s) A T hA hT hlow hupp
      _ = (M.card : ℝ)*SquareRootGramBound.cap N A T := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hMS) (SquareRootGramBound.cap_nonneg N A T)
  have hdiag : G r=(N : ℝ) := by
    have he := DirichletGramLargeValues.diagonal_norm (Ico N (2*N)) τ r
    have hc : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
    rw [hc] at he
    exact he
  have he := sum_erase_add R G hr
  have hf := Finset.sum_filter_add_sum_filter_not S (fun s ↦ |τ s-τ r| ≤ A) G
  change (∑ s ∈ S, G s)+G r=(∑ s ∈ R, G s) at he
  change (∑ s ∈ P, G s)+(∑ s ∈ M, G s)=(∑ s ∈ S, G s) at hf
  rw [hdiag] at he
  change (∑ s ∈ R, G s) ≤ _
  unfold rowBudget
  linarith only [he,hf,hpbound,hfar]

theorem analysis_bound {ι : Type*} (R : Finset ι) (τ : ι → ℝ) (T A : ℝ) (hT : 1 ≤ T) (hA : 1 ≤ A)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) :
    (∑ r ∈ R, ‖polynomial (Ico N (2*N)) a (fun n ↦ -Real.log n) (τ r)‖^2) ≤
      rowBudget N R.card A T*(∑ n ∈ Ico N (2*N), ‖a n‖^2) := by
  exact FiniteGramLargeValues.analysis_bound (Ico N (2*N)) R a
    (fun r n ↦ phase (-Real.log n) (τ r)) (rowBudget N R.card A T) (rowBudget_nonneg N R.card A T hA)
    (row_bound R τ T A hT hA htau hsep N hN)

theorem dirichlet_bound {ι : Type*} (R : Finset ι) (τ : ι → ℝ) (T A : ℝ) (hT : 1 ≤ T) (hA : 1 ≤ A)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) a (τ r)‖^2) ≤
      rowBudget N R.card A T*(∑ n ∈ Ico N (2*N), ‖a n/(n : ℂ)‖^2) :=
  analysis_bound R τ T A hT hA htau hsep N hN (fun n ↦ a n/(n : ℂ))
end PaperP1.MixedGramRowBound
