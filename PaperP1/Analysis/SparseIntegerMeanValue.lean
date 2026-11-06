module

public import PaperP1.Analysis.MixedGramRowBound
public import PaperP1.Analysis.SupportedCoefficientSquareBudget
public import PaperP1.Analysis.SparseGramEnvelope

set_option autoImplicit false
@[expose] public noncomputable section
universe u
namespace PaperP1.SparseIntegerMeanValue
open Finset PaperP1 Filter
open scoped Classical

theorem cap_height_mono (N : ℕ) (A T U : ℝ) (hTU : T ≤ U) :
    SquareRootGramBound.cap N A T ≤ SquareRootGramBound.cap N A U := by
  have hl := Real.log_natCast_nonneg N
  unfold SquareRootGramBound.cap
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right ?_ (by linarith : 0 ≤ 1+Real.log (N : ℝ))
  apply mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 128)
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : 2*T ≤ 2*U)) (Nat.cast_nonneg N)) le_rfl

theorem separation_properties (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ SparseGramEnvelope.separation N ∧
      (SparseGramEnvelope.separation N)^2 ≤ (N : ℝ) ∧
      SparseGramEnvelope.separation N ≤ (N : ℝ) := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 1 ≤ SparseGramEnvelope.separation N := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1/4)
  have h2 : (SparseGramEnvelope.separation N)^2=(N : ℝ)^(1/2 : ℝ) := by
    rw [SparseGramEnvelope.separation,← Real.rpow_two,← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have h3 := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1/2 : ℝ) ≤ 1)
  have h4 := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1/4 : ℝ) ≤ 1)
  simp only [Real.rpow_one] at h3 h4
  exact ⟨h1,h2.le.trans h3,h4⟩

theorem card_cap_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ R : ℕ,
      (R : ℝ) ≤ SparseGramEnvelope.cardEnvelope N → ∀ T : ℝ,
      T ≤ SparseGramEnvelope.height N →
      (R : ℝ)*SquareRootGramBound.cap N (SparseGramEnvelope.separation N) T ≤ ε*(N : ℝ) := by
  obtain ⟨N₀,hN₀,hs⟩ := SparseGramEnvelope.uniform_small ε hε
  refine ⟨N₀,hN₀,?_⟩
  intro N hN R hR T hT
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsmall := hs N hN
  unfold SparseGramEnvelope.normalizedCap at hsmall
  have hcardNN : 0 ≤ SparseGramEnvelope.cardEnvelope N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    _ ≤ SparseGramEnvelope.cardEnvelope N*SquareRootGramBound.cap N (SparseGramEnvelope.separation N) T :=
      mul_le_mul_of_nonneg_right hR (SquareRootGramBound.cap_nonneg _ _ _)
    _ ≤ SparseGramEnvelope.cardEnvelope N*SquareRootGramBound.cap N (SparseGramEnvelope.separation N) (SparseGramEnvelope.height N) :=
      mul_le_mul_of_nonneg_left (cap_height_mono N _ _ _ hT) hcardNN
    _ ≤ _ := (div_le_iff₀ hNp).mp hsmall

theorem budget_bound_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ R : ℕ,
      (R : ℝ) ≤ SparseGramEnvelope.cardEnvelope N → ∀ T : ℝ,
      T ≤ SparseGramEnvelope.height N →
      MixedGramRowBound.rowBudget N R (SparseGramEnvelope.separation N) T ≤
        10*(N : ℝ)*(1+Real.log (N : ℝ)) := by
  obtain ⟨N₀,hN₀,hs⟩ := card_cap_uniform 1 (by norm_num)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN R hR T hT
  have hn : 1 ≤ N := by omega
  obtain ⟨hA,hA2,hAN⟩ := separation_properties N hn
  have hcap := hs N hN R hR T hT
  rw [one_mul] at hcap
  have hlog := Real.log_le_log (show 0 < SparseGramEnvelope.separation N by linarith) hAN
  have h6 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hlog) (show 0 ≤ 6*(N : ℝ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hA2 (by norm_num : (0 : ℝ) ≤ 2)
  have hp := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Real.log_natCast_nonneg N)
  unfold MixedGramRowBound.rowBudget
  nlinarith only [hcap,h6,h2,hp]

theorem sampled_bound_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ {ι : Type u} (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      1 ≤ T → T ≤ SparseGramEnvelope.height N →
      (R.card : ℝ) ≤ SparseGramEnvelope.cardEnvelope N →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ a : ℕ → ℂ,
      (∑ r ∈ R, ‖GaussianExponentialSums.polynomial (Ico N (2*N)) a (fun n ↦ -Real.log n) (τ r)‖^2) ≤
        10*(N : ℝ)*(1+Real.log (N : ℝ))*(∑ n ∈ Ico N (2*N), ‖a n‖^2) := by
  obtain ⟨N₀,hN₀,hb⟩ := budget_bound_uniform
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ι R τ T hT hTU hR htau hsep a
  have hNp : 0 < N := by omega
  have hA := (separation_properties N (by omega)).1
  have hh := MixedGramRowBound.analysis_bound R τ T (SparseGramEnvelope.separation N) hT hA htau hsep N hNp a
  exact hh.trans (mul_le_mul_of_nonneg_right (hb N hN R.card hR T hTU) (sum_nonneg (fun _n _hn ↦ sq_nonneg _)))

theorem dirichlet_unit_uniform :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ {ι : Type u} (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      1 ≤ T → T ≤ SparseGramEnvelope.height N →
      (R.card : ℝ) ≤ SparseGramEnvelope.cardEnvelope N →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ f : ℕ → ℂ, (∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f (τ r)‖^2) ≤
        10*(1+Real.log (N : ℝ)) := by
  obtain ⟨N₀,hN₀,hs⟩ := sampled_bound_uniform.{u}
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ι R τ T hT hTU hR htau hsep f hf
  have hNp : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hh := hs N hN R τ T hT hTU hR htau hsep (fun n ↦ f n/(n : ℂ))
  have hc := SupportedCoefficientSquareBudget.support_square_budget N hNp (Ico N (2*N)) (Ico N (2*N))
    (fun _n hn ↦ hn) (fun _n hn ↦ hn) f hf (fun _n hn hnot ↦ False.elim (hnot hn))
  have hcard : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
  rw [hcard] at hc
  have heq : (N : ℝ)/(N : ℝ)^2=1/(N : ℝ) := by field_simp
  rw [heq] at hc
  have hlogN := Real.log_natCast_nonneg N
  calc
    _ ≤ 10*(N : ℝ)*(1+Real.log (N : ℝ))*(∑ n ∈ Ico N (2*N), ‖f n/(n : ℂ)‖^2) := hh
    _ ≤ 10*(N : ℝ)*(1+Real.log (N : ℝ))*(1/(N : ℝ)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by field_simp
end PaperP1.SparseIntegerMeanValue
