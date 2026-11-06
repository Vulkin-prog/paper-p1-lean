module

public import PaperP1.Analysis.RamareRemainderMeanValue

/-! # Exact actual Dirichlet quotient decomposition with a uniform negligible difference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirichletRamareApproximation
open Finset PaperP1 LogarithmicPhase GaussianExponentialSums DirichletPolynomialMeanValue
open scoped Classical

def twist (f : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ := f n/(n : ℂ)*phase (-Real.log n) t

theorem twist_mul (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) (m n : ℕ) :
    twist f (m*n) t=twist f m t*twist f n t := by
  by_cases hm : m=0
  · subst m; simp [twist]
  by_cases hn : n=0
  · subst n; simp [twist]
  have hphase : phase (-Real.log ((m*n : ℕ) : ℝ)) t = phase (-Real.log m) t*phase (-Real.log n) t := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn),neg_add,phase_add]
  rw [twist,hf,Nat.cast_mul,hphase,twist,twist]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem twist_norm (f : ℕ → ℂ) (n : ℕ) (t : ℝ) : ‖twist f n t‖=‖f n‖/(n : ℝ) := by
  rw [twist,norm_mul,norm_div,phase_norm,mul_one,Complex.norm_natCast]

theorem twist_continuous (f : ℕ → ℂ) (n : ℕ) : Continuous (twist f n) := by
  exact continuous_const.mul (phase_continuous (-Real.log n))

def quotient (N : ℕ) (P : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ Icc 1 (2*N/p),
    if p*m ∈ Ico N (2*N) then
      twist f p t*twist f m t/((PrimeDivisorWeights.count P m+1 : ℕ) : ℂ) else 0

theorem exact_with_remainder (N : ℕ) (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    value (Ico N (2*N)) f t = quotient N P f t +
      value (Ico N (2*N)) (RamareRemainderMeanValue.coefficient P f) t := by
  have hh := RamareWeights.full_ramare_with_remainder (Ico N (2*N)) P (2*N) hP
    (fun n hn ↦ ⟨hN.trans_le (mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩)
    (fun n ↦ twist f n t) (twist_mul f hf t)
  calc
    _ = ∑ n ∈ Ico N (2*N), twist f n t := rfl
    _ = quotient N P f t + ∑ n ∈ Ico N (2*N), ((1-RamareWeights.weight P n : ℝ) : ℂ)*twist f n t := hh
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro n hn
      simp only [twist,RamareRemainderMeanValue.coefficient,div_eq_mul_inv]
      ring

theorem difference_identity (N : ℕ) (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    value (Ico N (2*N)) f t-quotient N P f t =
      value (Ico N (2*N)) (RamareRemainderMeanValue.coefficient P f) t := by
  rw [exact_with_remainder N hN P hP f hf t]
  abel

theorem quotient_continuous (N : ℕ) (P : Finset ℕ) (f : ℕ → ℂ) : Continuous (quotient N P f) := by
  apply continuous_finsetSum
  intro p hp
  apply continuous_finsetSum
  intro m hm
  by_cases hmem : p*m ∈ Ico N (2*N)
  · simp only [ite_eq_left hmem]
    exact ((twist_continuous f p).mul (twist_continuous f m)).div_const _
  · simpa only [ite_eq_right hmem] using (continuous_const : Continuous (fun _t : ℝ ↦ (0 : ℂ)))

theorem difference_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ f : ℕ → ℂ, (∀ a b, f (a*b)=f a*f b) →
      (∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-
        quotient N (SlowPrimeBandSieve.primes N) f t‖^2) ≤ ε := by
  obtain ⟨N₀,hN₀,hs⟩ := RamareRemainderMeanValue.remainder_small_uniform ε hε
  refine ⟨N₀,hN₀,?_⟩
  intro N hN f hf hbound T hT hTN
  have hNp : 0 < N := by omega
  have he (t : ℝ) := difference_identity N hNp (SlowPrimeBandSieve.primes N)
    (fun p hp ↦ (mem_filter.mp hp).2) f hf t
  simp_rw [he]
  exact hs N hN f hbound T hT hTN
end DirichletRamareApproximation
