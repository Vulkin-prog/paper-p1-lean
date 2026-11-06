module

public import PaperP1.Analysis.SpacedShiftDifferencing
public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.IteratedLogarithmicCorrelation
public import PaperP1.Analysis.IteratedLogarithmicPhase

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RecursiveLogarithmicDifferencing
open Finset Filter PaperP1 IteratedLogarithmicCorrelation
open scoped Classical

def budget (K : ℕ) : ℕ → ℝ → ℝ
  | 0,ε => ε
  | n+1,ε => Real.sqrt (2/(K : ℝ)+2*budget K n ε)

theorem budget_nonneg (K n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) : 0 ≤ budget K n ε := by
  cases n with
  | zero => exact hε
  | succ n => exact Real.sqrt_nonneg _

theorem budget_monotone (K n : ℕ) (ε δ : ℝ) (hεδ : ε ≤ δ) : budget K n ε ≤ budget K n δ := by
  induction n with
  | zero => exact hεδ
  | succ n ih => exact Real.sqrt_le_sqrt (by linarith only [ih])

theorem budget_tendsto (n : ℕ) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0)) : Tendsto (fun X ↦ budget (κ X) n (ε X)) atTop (nhds 0) := by
  induction n with
  | zero => exact hε
  | succ n ih =>
    have hInv : Tendsto (fun X ↦ 2/(κ X : ℝ)) atTop (nhds 0) := by
      simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
        (tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hκ)).const_mul 2
    have hSum : Tendsto (fun X ↦ 2/(κ X : ℝ)+2*budget (κ X) n (ε X)) atTop (nhds 0) := by
      simpa only [add_zero,mul_zero] using hInv.add (ih.const_mul 2)
    simpa only [budget,Function.comp_def,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hSum

theorem iterate_bound (X A K : ℕ) (hA : 0 < A) (hK : 0 < K) (hSpan : A*K ≤ X)
    (t ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    ∀ hs : List ℝ,
      (∀ us : List ℝ, us.length=n → (∀ h ∈ us, (A : ℝ) ≤ h ∧ h ≤ ((A*K : ℕ) : ℝ)) →
        ∀ L ≤ X, ‖∑ j ∈ range L, sequence (us++hs) t X j‖ ≤ (X : ℝ)*ε) →
      ∀ L ≤ X, ‖∑ j ∈ range L, sequence hs t X j‖ ≤ (X : ℝ)*budget K n ε := by
  induction n with
  | zero =>
    intro hs hLeaf L hL
    simpa only [budget,List.nil_append] using hLeaf [] rfl (by simp) L hL
  | succ n ih =>
    intro hs hLeaf L hLX
    have hBudget := budget_nonneg K n ε hε
    have hE : 0 ≤ (X : ℝ)*budget K n ε := mul_nonneg (Nat.cast_nonneg X) hBudget
    have hCorr (d : ℕ) (hDA : A ≤ d) (hdAK : d < A*K) :
        ‖ShiftedCorrelations.correlation L (sequence hs t X) d‖ ≤ (X : ℝ)*budget K n ε := by
      rw [correlation_sequence_identity]
      apply ih ((d : ℝ)::hs) ?_ (L-d) ((Nat.sub_le L d).trans hLX)
      intro us hLen hUs M hMX
      have hExtLen : (us++[(d : ℝ)]).length=n+1 := by simp only [List.length_append,List.length_singleton,hLen]
      have hExt : ∀ v ∈ us++[(d : ℝ)], (A : ℝ) ≤ v ∧ v ≤ ((A*K : ℕ) : ℝ) := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hUs v hv
        · have he : v=(d : ℝ) := List.mem_singleton.mp hv
          rw [he]
          exact ⟨by exact_mod_cast hDA,by exact_mod_cast hdAK.le⟩
      have hh := hLeaf (us++[(d : ℝ)]) hExtLen hExt M hMX
      simpa only [List.append_assoc,List.singleton_append] using hh
    have hRaw := SpacedShiftDifferencing.differencing_bound L A K hA hK (sequence hs t X)
      (fun j _hj ↦ (sequence_norm hs t X j).le) ((X : ℝ)*budget K n ε) hE hCorr
    have hSource : ((L+A*K : ℕ) : ℝ) ≤ 2*(X : ℝ) := by exact_mod_cast (show L+A*K ≤ 2*X by omega)
    have hLXR : (L : ℝ) ≤ X := by exact_mod_cast hLX
    have hDiv := div_le_div_of_nonneg_right hLXR (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    have hUpper := mul_le_mul hSource (add_le_add hDiv (le_refl ((X : ℝ)*budget K n ε)))
      (show 0 ≤ (L : ℝ)/(K : ℝ)+(X : ℝ)*budget K n ε by positivity) (by positivity : 0 ≤ 2*(X : ℝ))
    have hArg : 0 ≤ 2/(K : ℝ)+2*budget K n ε := by positivity
    have hEq : ((X : ℝ)*budget K (n+1) ε)^2=2*(X : ℝ)*((X : ℝ)/(K : ℝ)+(X : ℝ)*budget K n ε) := by
      rw [mul_pow,budget,Real.sq_sqrt hArg]
      ring
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg X) (budget_nonneg K (n+1) ε hε))).mp
    rw [hEq]
    exact hRaw.trans hUpper

theorem logarithmic_bound (X A K : ℕ) (hA : 0 < A) (hK : 0 < K) (hSpan : A*K ≤ X)
    (t ε : ℝ) (hε : 0 ≤ ε) (n : ℕ)
    (hLeaf : ∀ us : List ℝ, us.length=n → (∀ h ∈ us, (A : ℝ) ≤ h ∧ h ≤ ((A*K : ℕ) : ℝ)) →
      ∀ L ≤ X, ‖∑ j ∈ Ico X (X+L), IteratedLogarithmicPhase.function us t j‖ ≤ (X : ℝ)*ε) :
    ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤ (X : ℝ)*budget K n ε := by
  have hh := iterate_bound X A K hA hK hSpan t ε hε n [] (by
    intro us hLen hUs L hLX
    simpa only [List.append_nil,sequence_sum_identity] using hLeaf us hLen hUs L hLX) X le_rfl
  rw [sequence_sum_identity] at hh
  simpa only [IteratedLogarithmicPhase.function_nil,Nat.two_mul] using hh
end PaperP1.RecursiveLogarithmicDifferencing
