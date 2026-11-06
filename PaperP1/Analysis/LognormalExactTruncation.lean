module

public import PaperP1.Analysis.LognormalSumIntegrability
public import PaperP1.Analysis.LognormalPhaseVariation
public import PaperP1.Analysis.LognormalUpperTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalExactTruncation
open Finset Filter MeasureTheory PaperP1 LognormalPhaseVariation
open scoped Classical

theorem series_split (A t : ℝ) (hA : 0 < A) (M : ℕ) (hM : 1 ≤ M) :
    LognormalSumIntegrability.value A t=
      (∑ n ∈ Icc 1 (M-1), function A t n)+LognormalUpperTail.tail A t M := by
  have hSum := (LognormalSumIntegrability.summable_terms A t hA).sum_add_tsum_nat_add (M-1)
  have hSum' :
      (∑ k ∈ range (M-1), function A t ((k+1 : ℕ) : ℝ))+
      (∑' k : ℕ, function A t ((k+(M-1)+1 : ℕ) : ℝ))=LognormalSumIntegrability.value A t := hSum
  have hHead : (∑ n ∈ Icc 1 (M-1), function A t n)=
      ∑ k ∈ range (M-1), function A t ((k+1 : ℕ) : ℝ) := LognormalSumIntegrability.head_identity A t (M-1)
  have hTail : (∑' k : ℕ, function A t ((k+(M-1)+1 : ℕ) : ℝ))=LognormalUpperTail.tail A t M := by
    unfold LognormalUpperTail.tail
    apply tsum_congr
    intro k
    rw [show k+(M-1)+1=k+M by omega]
    rfl
  rw [← hHead,hTail] at hSum'
  exact hSum'.symm

theorem head_interval_split (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (a : ℕ → ℂ) :
    (∑ n ∈ Icc 1 (M-1), a n)=(∑ n ∈ Icc 1 (N-1), a n)+(∑ n ∈ Ico N M, a n) := by
  have hSetN : Ico 1 N=Icc 1 (N-1) := by
    rw [← Ico_add_one_right_eq_Icc]
    congr 1
    omega
  have hSetM : Ico 1 M=Icc 1 (M-1) := by
    rw [← Ico_add_one_right_eq_Icc]
    congr 1
    omega
  have hh := sum_Ico_consecutive a hN hNM
  rw [hSetN,hSetM] at hh
  exact hh.symm

theorem integral_split (A t N M : ℝ) (hA : 0 < A) (hN : 0 < N) (hM : 0 < M) :
    (∫ x in Set.Ioi (0 : ℝ), function A t x)=
      ((∫ x in (0 : ℝ)..N, function A t x)+(∫ x in N..M, function A t x))+
        (∫ x in Set.Ioi M, function A t x) := by
  have hF : IntegrableOn (function A t) (Set.Ioi 0) := LognormalSumIntegrability.integrand_integrable A t hA
  have hFN : IntegrableOn (function A t) (Set.Ioi N) := hF.mono_set (fun x hx ↦ hN.trans hx)
  have hFM : IntegrableOn (function A t) (Set.Ioi M) := hF.mono_set (fun x hx ↦ hM.trans hx)
  have hFirst := intervalIntegral.integral_interval_add_Ioi hF hFN
  have hSecond := intervalIntegral.integral_interval_add_Ioi hFN hFM
  rw [← hSecond] at hFirst
  simpa only [add_assoc] using hFirst.symm
end PaperP1.LognormalExactTruncation
