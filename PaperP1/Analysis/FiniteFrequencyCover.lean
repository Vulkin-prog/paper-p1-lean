module

public import PaperP1.Analysis.FiniteFibreSquareBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteFrequencyCover
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem cover_bound {ι : Type*} (J : Finset ι) (S : ι → Set ℝ) (E : Set ℝ) (T : ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (hgn : ∀ t, 0 ≤ g t)
    (hE : MeasurableSet E) (hEI : E ⊆ Set.Ioc (-T) T)
    (hS : ∀ j ∈ J, MeasurableSet (S j)) (hSI : ∀ j ∈ J, S j ⊆ Set.Ioc (-T) T)
    (hcover : E ⊆ ⋃ j ∈ J, S j) : (∫ t in E, g t) ≤ ∑ j ∈ J, ∫ t in S j, g t := by
  have hI : IntegrableOn g (Set.Ioc (-T) T) := (hg.intervalIntegrable (-T) T).1
  have hsn (j : ι) (t : ℝ) : 0 ≤ (S j).indicator g t := by
    by_cases ht : t ∈ S j
    · rw [Set.indicator_of_mem ht]
      exact hgn t
    · rw [Set.indicator_of_notMem ht]
  have hpoint (t : ℝ) : E.indicator g t ≤ ∑ j ∈ J, (S j).indicator g t := by
    by_cases ht : t ∈ E
    · obtain ⟨j,hj,hjt⟩ : ∃ j ∈ J, t ∈ S j := by
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hcover ht)
        obtain ⟨hj,hjt⟩ := Set.mem_iUnion.mp hj
        exact ⟨j,hj,hjt⟩
      rw [Set.indicator_of_mem ht]
      calc
        g t = (S j).indicator g t := (Set.indicator_of_mem hjt g).symm
        _ ≤ _ := single_le_sum (fun j hj ↦ hsn j t) hj
    · rw [Set.indicator_of_notMem ht]
      exact sum_nonneg (fun j hj ↦ hsn j t)
  have hsi : ∀ j ∈ J, Integrable ((S j).indicator g) (volume.restrict (Set.Ioc (-T) T)) :=
    fun j hj ↦ hI.indicator (hS j hj)
  have hi := integral_mono_ae (f := E.indicator g) (g := fun t ↦ ∑ j ∈ J, (S j).indicator g t)
    (hI.indicator hE) (integrable_finsetSum J hsi)
    (Filter.Eventually.of_forall hpoint)
  have hind (A : Set ℝ) (hA : MeasurableSet A) (hAI : A ⊆ Set.Ioc (-T) T) :
      (∫ t in Set.Ioc (-T) T, A.indicator g t)=∫ t in A, g t := by
    rw [setIntegral_indicator hA,Set.inter_eq_right.mpr hAI]
  calc
    _ = ∫ t in Set.Ioc (-T) T, E.indicator g t := (hind E hE hEI).symm
    _ ≤ ∫ t in Set.Ioc (-T) T, ∑ j ∈ J, (S j).indicator g t := hi
    _ = ∑ j ∈ J, ∫ t in Set.Ioc (-T) T, (S j).indicator g t := integral_finsetSum J hsi
    _ = _ := sum_congr rfl (fun j hj ↦ hind (S j) (hS j hj) (hSI j hj))

theorem finite_sum_cover_bound {ι κ : Type*} (J : Finset ι) (K : Finset κ)
    (F : κ → ℝ → ℂ) (hF : ∀ l ∈ K, Continuous (F l)) (E : Set ℝ) (T : ℝ)
    (S : ι → κ → Set ℝ) (b : κ → ℝ) (hE : MeasurableSet E) (hEI : E ⊆ Set.Ioc (-T) T)
    (hS : ∀ j ∈ J, ∀ l ∈ K, MeasurableSet (S j l))
    (hSI : ∀ j ∈ J, ∀ l ∈ K, S j l ⊆ Set.Ioc (-T) T)
    (hcover : ∀ l ∈ K, E ⊆ ⋃ j ∈ J, S j l)
    (hbudget : ∀ j ∈ J, ∀ l ∈ K, (∫ t in S j l, ‖F l t‖^2) ≤ b l) :
    (∫ t in E, ‖∑ l ∈ K, F l t‖^2) ≤ (J.card : ℝ)*(K.card : ℝ)*(∑ l ∈ K, b l) := by
  have hterm (l : κ) (hl : l ∈ K) : (∫ t in E, ‖F l t‖^2) ≤ (J.card : ℝ)*b l := by
    have hc := cover_bound J (fun j ↦ S j l) E T (fun t ↦ ‖F l t‖^2) ((hF l hl).norm.pow 2)
      (fun t ↦ sq_nonneg _) hE hEI (fun j hj ↦ hS j hj l hl) (fun j hj ↦ hSI j hj l hl) (hcover l hl)
    have hh := sum_le_sum (s := J) (fun j hj ↦ hbudget j hj l hl)
    rw [sum_const,nsmul_eq_mul] at hh
    exact hc.trans hh
  have hC : Continuous (fun t ↦ ‖∑ l ∈ K, F l t‖^2) :=
    (continuous_finsetSum K hF).norm.pow 2
  have hG : Continuous (fun t ↦ (K.card : ℝ)*(∑ l ∈ K, ‖F l t‖^2)) :=
    continuous_const.mul (continuous_finsetSum K (fun l hl ↦ (hF l hl).norm.pow 2))
  have hi := setIntegral_mono_on (μ := volume) (f := fun t ↦ ‖∑ l ∈ K, F l t‖^2)
    (g := fun t ↦ (K.card : ℝ)*(∑ l ∈ K, ‖F l t‖^2))
    ((hC.intervalIntegrable (-T) T).1.mono_set hEI) ((hG.intervalIntegrable (-T) T).1.mono_set hEI) hE
    (fun t ht ↦ FiniteFibreSquareBudget.norm_sum_sq_le_card K (fun l ↦ F l t))
  have hfi : ∀ l ∈ K, IntegrableOn (fun t ↦ ‖F l t‖^2) E :=
    fun l hl ↦ ((hF l hl).norm.pow 2 |>.intervalIntegrable (-T) T).1.mono_set hEI
  rw [integral_const_mul,integral_finsetSum K (f := fun l t ↦ ‖F l t‖^2) hfi] at hi
  have hs := sum_le_sum hterm
  rw [← mul_sum] at hs
  have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg K.card : (0 : ℝ) ≤ K.card)
  exact hi.trans (hh.trans_eq (by ring))
end PaperP1.FiniteFrequencyCover
