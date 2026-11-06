module

public import PaperP1.Analysis.ClippedPowerSum
public import PaperP1.Analysis.FullTriplePerron
public import PaperP1.Analysis.CommonDampedSum
public import PaperP1.Analysis.ValuationDamping

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CountWeightedSum
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

theorem coefficient_bound (c : ℂ) (hc : ‖c‖ ≤ 1) (k : ℕ) (n : ℕ) (τ : ℝ) :
    ‖(c/((k+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ‖ ≤ 1 := by
  rw [norm_mul,phase_norm,mul_one,norm_div,Complex.norm_natCast]
  exact (div_le_one (by positivity : (0 : ℝ) < (k+1 : ℕ))).mpr
    (hc.trans (by exact_mod_cast (show 1 ≤ k+1 by omega)))

theorem actual_difference_bound (X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (τ : ℝ) :
    ‖(∑ n ∈ Icc 1 X, ((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ)-
      (∑ n ∈ Icc 1 X, ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ)‖ ≤
      2*((PrimeDivisorWeights.squareExceptions P X).card : ℝ) := by
  let D := PrimeDivisorWeights.squareExceptions P X
  have he : (Icc 1 X).filter (fun n ↦ n ∈ D)=D := by
    ext n
    constructor
    · exact fun hn ↦ (mem_filter.mp hn).2
    · intro hn
      have hb := mem_Ioc.mp (mem_filter.mp hn).1
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,hb.2⟩,hn⟩
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 1 X, ‖((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ-
        ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 X, if n ∈ D then (2 : ℝ) else 0 := by
      apply sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := by have h := (mem_Icc.mp hn).1; omega
      have hfN : ‖(f n : ℂ)‖ ≤ 1 := FullTriplePerron.complexify_bound f hf n (by omega)
      by_cases hd : n ∈ D
      · rw [ite_eq_left hd]
        exact (norm_sub_le _ _).trans (by
          have h1 := coefficient_bound (f n) hfN (PrimeDivisorWeights.count P n) n τ
          have h2 := coefficient_bound (f n) hfN (ValuationDamping.multiplicity P n) n τ
          linarith)
      · rw [ite_eq_right hd]
        have hsq : ∀ p ∈ P, ¬p^2 ∣ n := by
          intro p hp hs
          apply hd
          exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,(mem_Icc.mp hn).2⟩,⟨p,hp,hs⟩⟩
        rw [ValuationDamping.multiplicity_eq_count P hP n hn0 hsq,sub_self,norm_zero]
    _ = 2*(D.card : ℝ) := by
      rw [← sum_filter,he,sum_const,nsmul_eq_mul]
      ring

theorem square_count_bound (P : Finset ℕ) (X : ℕ) (R : ℝ) (hR : 2 ≤ R)
    (hP : ∀ p ∈ P, R < (p : ℝ)) :
    ((PrimeDivisorWeights.squareExceptions P X).card : ℝ) ≤ 2*(X : ℝ)/R := by
  have ht := ClippedPowerSum.finite_tail_le_power P 2 R (by norm_num) (by linarith) hP
  have hs : (∑ p ∈ P, 1/(p : ℝ)^2) ≤ 2/R := by
    convert ht using 1
    · apply sum_congr rfl
      intro p hp
      norm_num [Real.rpow_neg,Real.rpow_two,div_eq_mul_inv]
    · norm_num [PowerSeriesTail.constant,Real.rpow_neg_one,div_eq_mul_inv]
  calc
    _ ≤ ∑ p ∈ P, ((X/p^2 : ℕ) : ℝ) := by
      exact_mod_cast PrimeDivisorWeights.square_exceptions_card P X
    _ ≤ ∑ p ∈ P, (X : ℝ)/(p : ℝ)^2 := by
      apply sum_le_sum
      intro p hp
      have hh : ((X/p^2 : ℕ) : ℝ) ≤ (X : ℝ)/((p^2 : ℕ) : ℝ) := Nat.cast_div_le
      convert hh using 1
      norm_cast
    _ = (X : ℝ)*∑ p ∈ P, 1/(p : ℝ)^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ (X : ℝ)*(2/R) := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg X)
    _ = _ := by ring

theorem common_count_weighted_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ T : ℝ, 1 ≤ T →
      (ActualEulerBand.frequencyCutoff X : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
          ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
          ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖∑ n ∈ Icc 1 X,
            ((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀,hs⟩ := CommonDampedSum.common_weighted_summatory_small (ε/2) δ (by positivity) hδ
  let R := max 2 (8/ε)
  have hR : 2 ≤ R := le_max_left _ _
  have hRp : 0 < R := by linarith
  have hsmall : 4/R ≤ ε/2 := by
    apply (div_le_iff₀ hRp).mpr
    have hh := (div_le_iff₀ hε).mp (le_max_right 2 (8/ε))
    nlinarith
  refine ⟨R,hR,X₀,hX₀,?_⟩
  intro X hX T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs X hX T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro P hP f hf τ hτ hnot
  have hv := hoff P f hf τ hτ hnot
  have hd := actual_difference_bound X P (fun p hp ↦ (hP p hp).1) f hf τ
  have hc := square_count_bound P X R hR (fun p hp ↦ (hP p hp).2)
  let A := ∑ n ∈ Icc 1 X, ((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ
  let B := ∑ n ∈ Icc 1 X, ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ
  have hnorm : ‖A‖ ≤ ‖A-B‖+‖B‖ := by
    simpa only [sub_add_cancel] using norm_add_le (A-B) B
  dsimp only [A,B] at hnorm
  have hscale := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
  have herr : 2*((PrimeDivisorWeights.squareExceptions P X).card : ℝ) ≤ (ε/2)*(X : ℝ) := by
    calc
      _ ≤ 2*(2*(X : ℝ)/R) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = (4/R)*(X : ℝ) := by ring
      _ ≤ _ := hscale
  linarith only [hnorm,hd,hv,herr]
end PaperP1.CountWeightedSum
