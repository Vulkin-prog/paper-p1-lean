module

public import PaperP1.Arithmetic.LocalPrimeSieve
public import Mathlib.Analysis.Complex.Exponential
public import PaperP1.Analysis.GaussianFrequencyRowBound

/-! # Actual logarithmic prime-window mass and weighted Gaussian frequency rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeLogFrequencyRows
open Finset Nat MeasureTheory PaperP1
open scoped Classical ComplexConjugate

theorem exp_small_bound (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) : Real.exp u ≤ 1+2*u := by
  have hh := Real.abs_exp_sub_one_le (show |u| ≤ 1 by rwa [abs_of_nonneg hu])
  rw [abs_of_nonneg hu] at hh
  linarith [le_abs_self (Real.exp u-1)]

theorem short_log_window_mass (S : Finset ℕ) (T : ℝ) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ T^2 ≤ (p : ℝ))
    (hgap : ∀ p ∈ S, ∀ q ∈ S, |Real.log (p : ℝ)-Real.log (q : ℝ)| ≤ 1/T) :
    (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)) ≤ 200/T := by
  have hTpos : 0 < T := by linarith
  by_cases hne : S.Nonempty
  · let A := S.min' hne
    have hAmem : A ∈ S := S.min'_mem hne
    have hAprime := (hS A hAmem).1
    have hA0 : (0 : ℝ) < A := by exact_mod_cast hAprime.pos
    have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hAprime.one_le
    have hbase := (hS A hAmem).2
    have hTA : T ≤ A := by nlinarith
    let U : ℝ := (A : ℝ)/T
    have hU1 : 1 ≤ U := (one_le_div hTpos).mpr hTA
    have hUA : U ≤ A := by
      dsimp only [U]
      exact div_le_self hA0.le hT
    have hU2 : (A : ℝ) ≤ U^2 := by
      dsimp only [U]
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hTpos)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hbase hA0.le]
    let H := ⌈4*U⌉₊
    have hHlow : 4*U ≤ (H : ℝ) := Nat.le_ceil _
    have hHhigh : (H : ℝ) ≤ 4*U+1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*U)).le
    have hH2 : 2 ≤ H := by exact_mod_cast (show (2 : ℝ) ≤ H by linarith)
    have hwidth : A+H ≤ H^2 := by
      have hHsq : 16*U^2 ≤ (H : ℝ)^2 := by nlinarith [sq_nonneg ((H : ℝ)-4*U)]
      exact_mod_cast (show (A : ℝ)+(H : ℝ) ≤ (H : ℝ)^2 by nlinarith)
    have hsub : S ⊆ (Ico A (A+H)).filter Nat.Prime := by
      intro p hp
      have hpprime := (hS p hp).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      have hpA : A ≤ p := S.min'_le p hp
      have hlogp : Real.log (p : ℝ) ≤ Real.log (A : ℝ)+1/T := by
        have hh := hgap p hp A hAmem
        linarith [le_abs_self (Real.log (p : ℝ)-Real.log (A : ℝ))]
      have he : (p : ℝ) ≤ (A : ℝ)*Real.exp (1/T) := by
        calc
          _ = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hp0).symm
          _ ≤ Real.exp (Real.log (A : ℝ)+1/T) := Real.exp_le_exp.mpr hlogp
          _ = _ := by rw [Real.exp_add,Real.exp_log hA0]
      have hexp := exp_small_bound (1/T) (by positivity) ((div_le_one hTpos).mpr hT)
      have hpshort : (p : ℝ) < (A+H : ℕ) := by
        have hprod := mul_le_mul_of_nonneg_left hexp hA0.le
        have hAU : (A : ℝ)*(1+2*(1/T))=(A : ℝ)+2*U := by dsimp only [U]; ring
        rw [hAU] at hprod
        push_cast
        linarith
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hpA,by exact_mod_cast hpshort⟩,hpprime⟩
    calc
      _ ≤ ∑ p ∈ (Ico A (A+H)).filter Nat.Prime, Real.log (p : ℝ)/(p : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro p hp hnot
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le))
          (Nat.cast_nonneg p)
      _ ≤ 40*(H : ℝ)/(A : ℝ) := LocalPrimeSieve.interval_prime_reciprocal_log_weight A H hAprime.one_le hH2 hwidth
      _ ≤ 200/T := by
        have hHfive : (H : ℝ) ≤ 5*U := by linarith
        have he : 40*(5*U)/(A : ℝ)=200/T := by dsimp only [U]; field_simp; ring
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHfive (by norm_num)) hA0.le).trans_eq he
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,sum_empty]
    positivity

def bin (T w : ℝ) (p : ℕ) : ℕ := ⌊T*|Real.log (p : ℝ)-w|⌋₊

theorem floor_gap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : ⌊a⌋₊=⌊b⌋₊) : |a-b| ≤ 1 := by
  have ha0 := Nat.floor_le ha
  have hb0 := Nat.floor_le hb
  have ha1 := Nat.lt_floor_add_one a
  have hb1 := Nat.lt_floor_add_one b
  rw [← he] at hb0 hb1
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem same_bin_gap (T w : ℝ) (hT : 0 < T) (p q : ℕ) (he : bin T w p=bin T w q)
    (hsign : (w ≤ Real.log (p : ℝ) ∧ w ≤ Real.log (q : ℝ)) ∨
      (Real.log (p : ℝ) ≤ w ∧ Real.log (q : ℝ) ≤ w)) :
    |Real.log (p : ℝ)-Real.log (q : ℝ)| ≤ 1/T := by
  have hh := floor_gap (T*|Real.log (p : ℝ)-w|) (T*|Real.log (q : ℝ)-w|)
    (by positivity) (by positivity) he
  have hab : abs (T*abs (Real.log (p : ℝ)-w)-T*abs (Real.log (q : ℝ)-w))=
      T*abs (Real.log (p : ℝ)-Real.log (q : ℝ)) := by
    rcases hsign with ⟨hp,hq⟩ | ⟨hp,hq⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr hp),abs_of_nonneg (sub_nonneg.mpr hq)]
      have heq : T*(Real.log (p : ℝ)-w)-T*(Real.log (q : ℝ)-w)=T*(Real.log (p : ℝ)-Real.log (q : ℝ)) := by ring
      rw [heq,abs_mul,abs_of_pos hT]
    · rw [abs_of_nonpos (sub_nonpos.mpr hp),abs_of_nonpos (sub_nonpos.mpr hq)]
      have heq : T*(-(Real.log (p : ℝ)-w))-T*(-(Real.log (q : ℝ)-w))=-(T*(Real.log (p : ℝ)-Real.log (q : ℝ))) := by ring
      rw [heq,abs_neg,abs_mul,abs_of_pos hT]
  rw [hab] at hh
  exact (le_div_iff₀ hT).mpr (by nlinarith)

theorem bin_mass (S : Finset ℕ) (T w : ℝ) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ T^2 ≤ (p : ℝ)) (j : ℕ) :
    (∑ p ∈ S.filter (fun p ↦ bin T w p=j), Real.log (p : ℝ)/(p : ℝ)) ≤ 400/T := by
  let B := S.filter (fun p ↦ bin T w p=j)
  have hTpos : 0 < T := by linarith
  have hr := short_log_window_mass (B.filter (fun p : ℕ ↦ w ≤ Real.log (p : ℝ))) T hT
    (fun p hp ↦ hS p (mem_filter.mp (mem_filter.mp hp).1).1) (by
      intro p hp q hq
      have hp' := mem_filter.mp hp
      have hq' := mem_filter.mp hq
      exact same_bin_gap T w hTpos p q
        ((mem_filter.mp hp'.1).2.trans (mem_filter.mp hq'.1).2.symm) (Or.inl ⟨hp'.2,hq'.2⟩))
  have hl := short_log_window_mass (B.filter (fun p : ℕ ↦ ¬w ≤ Real.log (p : ℝ))) T hT
    (fun p hp ↦ hS p (mem_filter.mp (mem_filter.mp hp).1).1) (by
      intro p hp q hq
      have hp' := mem_filter.mp hp
      have hq' := mem_filter.mp hq
      exact same_bin_gap T w hTpos p q
        ((mem_filter.mp hp'.1).2.trans (mem_filter.mp hq'.1).2.symm)
        (Or.inr ⟨(lt_of_not_ge hp'.2).le,(lt_of_not_ge hq'.2).le⟩))
  have he := sum_filter_add_sum_filter_not B (fun p ↦ w ≤ Real.log (p : ℝ))
    (fun p ↦ Real.log (p : ℝ)/(p : ℝ))
  change (∑ p ∈ B, Real.log (p : ℝ)/(p : ℝ)) ≤ _
  calc
    _ = (∑ p ∈ B.filter (fun p : ℕ ↦ w ≤ Real.log (p : ℝ)), Real.log (p : ℝ)/(p : ℝ))+
        (∑ p ∈ B.filter (fun p : ℕ ↦ ¬w ≤ Real.log (p : ℝ)), Real.log (p : ℝ)/(p : ℝ)) := he.symm
    _ ≤ 200/T+200/T := add_le_add hr hl
    _ = _ := by ring

theorem gaussian_row (S : Finset ℕ) (T w : ℝ) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ T^2 ≤ (p : ℝ)) :
    (∑ p ∈ S, (Real.log (p : ℝ)/(p : ℝ))*Real.exp (-T^2*(Real.log (p : ℝ)-w)^2/4)) ≤
      (400/T)*(1+2*Real.sqrt Real.pi) := by
  let J := S.image (bin T w)
  let k : ℕ → ℝ := fun j ↦ Real.exp (-(1/4 : ℝ)*(j : ℝ)^2)
  have hTpos : 0 < T := by linarith
  have hpoint (p : ℕ) (hp : p ∈ S) :
      Real.exp (-T^2*(Real.log (p : ℝ)-w)^2/4) ≤ k (bin T w p) := by
    have hf : (bin T w p : ℝ) ≤ T*|Real.log (p : ℝ)-w| := Nat.floor_le (by positivity)
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (bin T w p)) hf 2
    rw [mul_pow,sq_abs] at hsq
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfibre := sum_fiberwise_of_maps_to (s := S) (t := J)
    (fun p hp ↦ mem_image_of_mem (bin T w) hp)
    (fun p ↦ (Real.log (p : ℝ)/(p : ℝ))*k (bin T w p))
  calc
    _ ≤ ∑ p ∈ S, (Real.log (p : ℝ)/(p : ℝ))*k (bin T w p) := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hpoint p hp)
        (div_nonneg (Real.log_nonneg (by exact_mod_cast (hS p hp).1.one_le)) (Nat.cast_nonneg p))
    _ = ∑ j ∈ J, ∑ p ∈ S.filter (fun p ↦ bin T w p=j),
        (Real.log (p : ℝ)/(p : ℝ))*k j := by
      rw [← hfibre]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro p hp
      rw [(mem_filter.mp hp).2]
    _ ≤ ∑ j ∈ J, (400/T)*k j := by
      apply sum_le_sum
      intro j hj
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (bin_mass S T w hT hS j) (Real.exp_pos _).le
    _ = (400/T)*∑ j ∈ J, k j := by rw [mul_sum]
    _ ≤ (400/T)*(1+Real.sqrt (Real.pi/(1/4 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := GaussianFrequencyRowBound.integer_row_bound J 0 (1/4) (by norm_num)
      simpa only [Nat.cast_zero,sub_zero,k] using hh
    _ = _ := by
      have he : Real.sqrt (Real.pi/(1/4 : ℝ))=2*Real.sqrt Real.pi := by
        have heq : Real.pi/(1/4 : ℝ)=Real.pi*(2 : ℝ)^2 := by ring
        rw [heq,Real.sqrt_mul Real.pi_pos.le,Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [he]
end PaperP1.PrimeLogFrequencyRows


