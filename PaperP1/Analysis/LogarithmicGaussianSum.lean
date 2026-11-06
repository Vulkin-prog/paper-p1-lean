module

public import PaperP1.Analysis.GaussianFrequencyRowBound
public import PaperP1.Arithmetic.IntegerRealIntervalCount
public import PaperP1.PNT.LogGrowth

/-! # Uniform actual integer Gaussian sums with quadratic logarithmic weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicGaussianSum
open Finset MeasureTheory PaperP1 Filter
open scoped Classical Topology

theorem natural_interval_card (S : Finset ℕ) (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) : (S.card : ℝ) ≤ b-a+1 := by
  have hinj : Function.Injective (fun n : ℕ ↦ (n : ℤ)) := by
    intro m n he
    change (m : ℤ)=(n : ℤ) at he
    omega
  have hh := IntegerRealIntervalCount.interval_card (S.image (fun n : ℕ ↦ (n : ℤ))) a b hab (by
    intro z hz
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
    simpa only [Int.cast_natCast] using hS n hn)
  simpa only [card_image_of_injective S hinj] using hh

theorem small_exp_bound (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : Real.exp δ ≤ 1+2*δ := by
  have hh := Real.abs_exp_sub_one_le (show |δ| ≤ 1 by rwa [abs_of_nonneg hδ])
  rw [abs_of_nonneg hδ] at hh
  linarith [le_abs_self (Real.exp δ-1)]

theorem exp_interval_card (S : Finset ℕ) (X L δ : ℝ) (hX : 0 ≤ X)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hS : ∀ n ∈ S, X*Real.exp L ≤ (n : ℝ) ∧ (n : ℝ) ≤ X*Real.exp (L+δ)) :
    (S.card : ℝ) ≤ 2*δ*X*Real.exp (L+δ)+1 := by
  have hexp : Real.exp L ≤ Real.exp (L+δ) := Real.exp_le_exp.mpr (by linarith)
  have horder := mul_le_mul_of_nonneg_left hexp hX
  have hh := natural_interval_card S (X*Real.exp L) (X*Real.exp (L+δ)) horder hS
  have hs := small_exp_bound δ hδ hδ1
  have hwidth : X*Real.exp (L+δ)-X*Real.exp L ≤ 2*δ*X*Real.exp L := by
    rw [Real.exp_add]
    have hp := mul_le_mul_of_nonneg_left hs (mul_nonneg hX (Real.exp_pos L).le)
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2*δ*X)
  linarith

theorem exp_log_quotient (X : ℝ) (n : ℕ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℝ)=X*Real.exp (Real.log ((n : ℝ)/X)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.exp_log (div_pos hnR hX)]
  field_simp

theorem log_annulus_card (S : Finset ℕ) (X δ : ℝ) (j : ℕ) (hX : 0 < X)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hS : ∀ n ∈ S, 0 < n ∧ (j : ℝ)*δ ≤ |Real.log ((n : ℝ)/X)| ∧
      |Real.log ((n : ℝ)/X)| ≤ ((j+1 : ℕ) : ℝ)*δ) :
    (S.card : ℝ) ≤ 4*δ*X*Real.exp (((j+1 : ℕ) : ℝ)*δ)+2 := by
  let P := S.filter (fun n : ℕ ↦ 0 ≤ Real.log ((n : ℝ)/X))
  let M := S.filter (fun n : ℕ ↦ ¬0 ≤ Real.log ((n : ℝ)/X))
  have hP := exp_interval_card P X ((j : ℝ)*δ) δ hX.le hδ hδ1 (by
    intro n hn
    have hn' := mem_filter.mp hn
    have hh := hS n hn'.1
    have hl := hh.2.1
    have hu := hh.2.2
    rw [abs_of_nonneg hn'.2] at hl hu
    have he : ((j+1 : ℕ) : ℝ)*δ=(j : ℝ)*δ+δ := by push_cast; ring
    rw [he] at hu
    rw [exp_log_quotient X n hX hh.1]
    exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hl) hX.le,
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu) hX.le⟩)
  have hM := exp_interval_card M X (-((j+1 : ℕ) : ℝ)*δ) δ hX.le hδ hδ1 (by
    intro n hn
    have hn' := mem_filter.mp hn
    have hh := hS n hn'.1
    have hl := hh.2.1
    have hu := hh.2.2
    rw [abs_of_nonpos (not_le.mp hn'.2).le] at hl hu
    rw [exp_log_quotient X n hX hh.1]
    refine ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hX.le,?_⟩
    apply mul_le_mul_of_nonneg_left _ hX.le
    apply Real.exp_le_exp.mpr
    push_cast at *
    nlinarith)
  have he : (j : ℝ)*δ+δ=((j+1 : ℕ) : ℝ)*δ := by push_cast; ring
  rw [he] at hP
  have hExp : Real.exp (-((j+1 : ℕ) : ℝ)*δ+δ) ≤ Real.exp (((j+1 : ℕ) : ℝ)*δ) := by
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hM' : (M.card : ℝ) ≤ 2*δ*X*Real.exp (((j+1 : ℕ) : ℝ)*δ)+1 :=
    hM.trans (add_le_add (mul_le_mul_of_nonneg_left hExp (by positivity)) le_rfl)
  have hcount := sum_filter_add_sum_filter_not S (fun n : ℕ ↦ 0 ≤ Real.log ((n : ℝ)/X)) (fun _ ↦ (1 : ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at hcount
  change (P.card : ℝ)+(M.card : ℝ)=(S.card : ℝ) at hcount
  linarith

def bin (X δ : ℝ) (n : ℕ) : ℕ := ⌊|Real.log ((n : ℝ)/X)|/δ⌋₊

theorem bin_bounds (X δ : ℝ) (n : ℕ) (hδ : 0 < δ) :
    (bin X δ n : ℝ)*δ ≤ |Real.log ((n : ℝ)/X)| ∧
      |Real.log ((n : ℝ)/X)| ≤ ((bin X δ n+1 : ℕ) : ℝ)*δ := by
  have hh := Nat.floor_le (div_nonneg (abs_nonneg (Real.log ((n : ℝ)/X))) hδ.le)
  have hl := Nat.lt_floor_add_one (|Real.log ((n : ℝ)/X)|/δ)
  refine ⟨(le_div_iff₀ hδ).mp hh,?_⟩
  have hu := (div_lt_iff₀ hδ).mp hl
  simpa only [bin,Nat.cast_add,Nat.cast_one] using hu.le

theorem bin_card (S : Finset ℕ) (X δ : ℝ) (j : ℕ) (hX : 0 < X)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : ∀ n ∈ S, 0 < n) :
    ((S.filter (fun n ↦ bin X δ n=j)).card : ℝ) ≤
      4*δ*X*Real.exp (((j+1 : ℕ) : ℝ)*δ)+2 := by
  apply log_annulus_card _ X δ j hX hδ.le hδ1
  intro n hn
  have hn' := mem_filter.mp hn
  have hh := bin_bounds X δ n hδ
  rw [hn'.2] at hh
  exact ⟨hS n hn'.1,hh⟩

def logGaussian (X δ : ℝ) (n : ℕ) : ℝ := Real.exp (-(Real.log ((n : ℝ)/X))^2/(32*δ^2))

def constant : ℝ := (4*Real.exp 17+2)*(1+Real.sqrt (Real.pi/(1/64 : ℝ)))

theorem logGaussian_bin_bound (X δ : ℝ) (n : ℕ) (hδ : 0 < δ) :
    logGaussian X δ n ≤ Real.exp (-(1/32 : ℝ)*(bin X δ n : ℝ)^2) := by
  have hh := (bin_bounds X δ n hδ).1
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (bin X δ n : ℝ)*δ) hh 2
  rw [mul_pow,sq_abs] at hs
  have hd := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 32*δ^2)
  have he : ((bin X δ n : ℝ)^2*δ^2)/(32*δ^2)=(bin X δ n : ℝ)^2/32 := by field_simp
  rw [he] at hd
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ -((bin X δ n : ℝ)^2/32) := by simpa only [neg_div] using neg_le_neg hd
    _ = _ := by ring

theorem growth_gaussian_bound (δ : ℝ) (hδ1 : δ ≤ 1) (j : ℕ) :
    Real.exp (((j+1 : ℕ) : ℝ)*δ)*Real.exp (-(1/32 : ℝ)*(j : ℝ)^2) ≤
      Real.exp 17*Real.exp (-(1/64 : ℝ)*(j : ℝ)^2) := by
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hδ1 (Nat.cast_nonneg (α := ℝ) (j+1))
  push_cast at hh ⊢
  nlinarith [sq_nonneg ((j : ℝ)-32)]

theorem gaussian_bin_monotone (j : ℕ) :
    Real.exp (-(1/32 : ℝ)*(j : ℝ)^2) ≤ Real.exp (-(1/64 : ℝ)*(j : ℝ)^2) := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (j : ℝ)]

theorem finite_logGaussian_sum (S : Finset ℕ) (X δ : ℝ) (hX : 0 < X)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, logGaussian X δ n) ≤ constant*(δ*X+1) := by
  let J := S.image (bin X δ)
  let g : ℕ → ℝ := fun j ↦ Real.exp (-(1/32 : ℝ)*(j : ℝ)^2)
  let k : ℕ → ℝ := fun j ↦ Real.exp (-(1/64 : ℝ)*(j : ℝ)^2)
  have hf := sum_fiberwise_of_maps_to' (s := S) (t := J) (g := bin X δ)
    (fun n hn ↦ mem_image_of_mem (bin X δ) hn) g
  have he : (∑ n ∈ S, g (bin X δ n))=
      ∑ j ∈ J, ((S.filter (fun n ↦ bin X δ n=j)).card : ℝ)*g j := by
    simpa only [sum_const,nsmul_eq_mul] using hf.symm
  have hpoint (j : ℕ) : (4*δ*X*Real.exp (((j+1 : ℕ) : ℝ)*δ)+2)*g j ≤
      (4*δ*X*Real.exp 17+2)*k j := by
    have hg := growth_gaussian_bound δ hδ1 j
    have hk := gaussian_bin_monotone j
    calc
      _ = (4*δ*X)*(Real.exp (((j+1 : ℕ) : ℝ)*δ)*g j)+2*g j := by ring
      _ ≤ (4*δ*X)*(Real.exp 17*k j)+2*k j := add_le_add
        (mul_le_mul_of_nonneg_left hg (by positivity)) (mul_le_mul_of_nonneg_left hk (by norm_num))
      _ = _ := by ring
  have hrow : (∑ j ∈ J, k j) ≤ 1+Real.sqrt (Real.pi/(1/64 : ℝ)) := by
    simpa only [k,Nat.cast_zero,sub_zero] using GaussianFrequencyRowBound.integer_row_bound J 0 (1/64) (by norm_num)
  calc
    _ ≤ ∑ n ∈ S, g (bin X δ n) := sum_le_sum (fun n hn ↦ logGaussian_bin_bound X δ n hδ)
    _ = ∑ j ∈ J, ((S.filter (fun n ↦ bin X δ n=j)).card : ℝ)*g j := he
    _ ≤ ∑ j ∈ J, (4*δ*X*Real.exp (((j+1 : ℕ) : ℝ)*δ)+2)*g j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (bin_card S X δ j hX hδ hδ1 hS) (Real.exp_pos _).le
    _ ≤ ∑ j ∈ J, (4*δ*X*Real.exp 17+2)*k j := sum_le_sum (fun j hj ↦ hpoint j)
    _ = (4*δ*X*Real.exp 17+2)*∑ j ∈ J, k j := by rw [mul_sum]
    _ ≤ (4*δ*X*Real.exp 17+2)*(1+Real.sqrt (Real.pi/(1/64 : ℝ))) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ ≤ ((4*Real.exp 17+2)*(δ*X+1))*(1+Real.sqrt (Real.pi/(1/64 : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg hδ.le hX.le,Real.exp_pos 17]
    _ = _ := by dsimp only [constant]; ring

theorem constant_pos : 0 < constant := by dsimp only [constant]; positivity

theorem quadratic_gaussian_absorption (u δ : ℝ) (hδ : 0 < δ) :
    u^2*Real.exp (-u^2/(32*δ^2)) ≤ 128*δ^2*Real.exp (-u^2/(128*δ^2)) := by
  let z := u^2/(128*δ^2)
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hExp : z ≤ Real.exp (3*z) := by linarith [Real.add_one_le_exp (3*z)]
  have hm := mul_le_mul_of_nonneg_right hExp (Real.exp_pos (-4*z)).le
  rw [← Real.exp_add] at hm
  have he : 3*z+(-4*z)=-z := by ring
  rw [he] at hm
  have hr : u^2/(32*δ^2)=4*z := by dsimp only [z]; ring
  have hu : u^2=128*δ^2*z := by dsimp only [z]; field_simp
  simp only [neg_div]
  change u^2*Real.exp (-(u^2/(32*δ^2))) ≤ 128*δ^2*Real.exp (-z)
  rw [hr,← neg_mul]
  calc
    _ = (128*δ^2)*(z*Real.exp (-4*z)) := by rw [hu]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

theorem logGaussian_weighted_point (X δ : ℝ) (n : ℕ) (hX : 0 < X)
    (hδ : 0 < δ) (hn : 0 < n) :
    (Real.log (n : ℝ))^2*logGaussian X δ n ≤
      (2*(Real.log X)^2+256*δ^2)*logGaussian X (2*δ) n := by
  let u := Real.log ((n : ℝ)/X)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ)=Real.log X+u := by dsimp only [u]; rw [Real.log_div hnR.ne' hX.ne']; ring
  have hs : (Real.log (n : ℝ))^2 ≤ 2*(Real.log X)^2+2*u^2 := by
    rw [hlog]
    nlinarith [sq_nonneg (Real.log X-u)]
  have he : 32*(2*δ)^2=128*δ^2 := by ring
  have hg : logGaussian X δ n ≤ logGaussian X (2*δ) n := by
    rw [logGaussian,logGaussian,he]
    apply Real.exp_le_exp.mpr
    have hd : u^2/(128*δ^2) ≤ u^2/(32*δ^2) :=
      div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by nlinarith [sq_nonneg δ])
    simpa only [neg_div] using neg_le_neg hd
  have ha : u^2*logGaussian X δ n ≤ 128*δ^2*logGaussian X (2*δ) n := by
    simpa only [logGaussian,he] using quadratic_gaussian_absorption u δ hδ
  calc
    _ ≤ (2*(Real.log X)^2+2*u^2)*logGaussian X δ n :=
      mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le
    _ = 2*(Real.log X)^2*logGaussian X δ n+2*(u^2*logGaussian X δ n) := by ring
    _ ≤ 2*(Real.log X)^2*logGaussian X (2*δ) n+2*(128*δ^2*logGaussian X (2*δ) n) :=
      add_le_add (mul_le_mul_of_nonneg_left hg (by positivity)) (mul_le_mul_of_nonneg_left ha (by norm_num))
    _ = _ := by ring

theorem finite_weighted_logGaussian_sum (S : Finset ℕ) (X δ : ℝ) (hX : 0 < X)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, (Real.log (n : ℝ))^2*logGaussian X δ n) ≤
      512*constant*((Real.log X)^2+1)*(δ*X+1) := by
  have hsum := finite_logGaussian_sum S X (2*δ) hX (by positivity) (by linarith) hS
  have hc := constant_pos
  have hd1 : δ ≤ 1 := by linarith
  have hdsq := pow_le_pow_left₀ hδ.le hd1 2
  norm_num only [one_pow] at hdsq
  have hA : 2*(Real.log X)^2+256*δ^2 ≤ 256*((Real.log X)^2+1) := by nlinarith [sq_nonneg (Real.log X)]
  have hB : (2*δ)*X+1 ≤ 2*(δ*X+1) := by linarith
  calc
    _ ≤ ∑ n ∈ S, (2*(Real.log X)^2+256*δ^2)*logGaussian X (2*δ) n :=
      sum_le_sum (fun n hn ↦ logGaussian_weighted_point X δ n hX hδ (hS n hn))
    _ = (2*(Real.log X)^2+256*δ^2)*∑ n ∈ S, logGaussian X (2*δ) n := by rw [mul_sum]
    _ ≤ (2*(Real.log X)^2+256*δ^2)*(constant*((2*δ)*X+1)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (256*((Real.log X)^2+1))*(constant*(2*(δ*X+1))) :=
      mul_le_mul hA (mul_le_mul_of_nonneg_left hB hc.le) (by positivity) (by positivity)
    _ = _ := by ring

theorem reciprocal_log_sq (X : ℝ) (n : ℕ) (hX : 0 < X) (hn : 0 < n) :
    (Real.log (X/(n : ℝ)))^2=(Real.log ((n : ℝ)/X))^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div hX.ne' hnR.ne',Real.log_div hnR.ne' hX.ne']
  ring

theorem finite_reciprocal_weighted_sum (S : Finset ℕ) (X δ : ℝ) (hX : 0 < X)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, (Real.log (n : ℝ))^2*Real.exp (-(Real.log (X/(n : ℝ)))^2/(32*δ^2))) ≤
      512*constant*((Real.log X)^2+1)*(δ*X+1) := by
  have he : (∑ n ∈ S, (Real.log (n : ℝ))^2*Real.exp (-(Real.log (X/(n : ℝ)))^2/(32*δ^2)))=
      ∑ n ∈ S, (Real.log (n : ℝ))^2*logGaussian X δ n := by
    apply sum_congr rfl
    intro n hn
    rw [reciprocal_log_sq X n hX (hS n hn)]
    rfl
  rw [he]
  exact finite_weighted_logGaussian_sum S X δ hX hδ hδhalf hS

def width (X : ℕ) : ℝ := 1/(Real.log (X : ℝ))^8

def scaledBound (X : ℕ) : ℝ :=
  512*constant*((Real.log (X : ℝ))^2+1)*(width X+1/(X : ℝ))

theorem width_positive (X : ℕ) (hX : 2 ≤ X) : 0 < width X := by
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  dsimp only [width]
  positivity

theorem scaledBound_tendsto : Tendsto scaledBound atTop (nhds 0) := by
  have hnat : Tendsto (fun X : ℕ ↦ (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hnat
  have hi := tendsto_inv_atTop_zero.comp hlog
  have hx := tendsto_inv_atTop_zero.comp hnat
  have hl2 : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))^2/(X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Real.rpow_two,Function.comp_def] using
      (PNT.tendsto_pow_log_div_pow_atTop 1 2 zero_lt_one).comp hnat
  have hc := ((((hi.pow 6).add (hi.pow 8)).add hl2).add hx).const_mul (512*constant)
  have hc0 : Tendsto (fun X : ℕ ↦ 512*constant*((((Real.log (X : ℝ))⁻¹)^6+
      ((Real.log (X : ℝ))⁻¹)^8)+(Real.log (X : ℝ))^2/(X : ℝ)+(X : ℝ)⁻¹)) atTop (nhds 0) := by
    simpa only [Function.comp_def,zero_pow (by decide : (6 : ℕ) ≠ 0),zero_pow (by decide : (8 : ℕ) ≠ 0),
      zero_add,mul_zero] using hc
  have he : (fun X : ℕ ↦ 512*constant*((((Real.log (X : ℝ))⁻¹)^6+
      ((Real.log (X : ℝ))⁻¹)^8)+(Real.log (X : ℝ))^2/(X : ℝ)+(X : ℝ)⁻¹))=ᶠ[atTop] scaledBound := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
    have hl : Real.log (X : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).ne'
    dsimp only [scaledBound,width]
    field_simp [hX0,hl]
    ring
  exact hc0.congr' he

theorem integer_gaussian_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ S : Finset ℕ,
      (∀ n ∈ S, 0 < n) →
      (∑ n ∈ S, (Real.log (n : ℝ))^2*Real.exp (-(Real.log ((X : ℝ)/(n : ℝ)))^2/(32*(width X)^2))) ≤ ε*(X : ℝ) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    ((scaledBound_tendsto.eventually (eventually_lt_nhds hε)).and (hlog.eventually (eventually_ge_atTop 2)))
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX S hS
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hh := hX₀ X ((le_max_left _ _).trans hX)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlpos : 0 < Real.log (X : ℝ) := by linarith [hh.2]
  have hwidth : width X ≤ 1/2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hh.2 8
    norm_num only [show (2 : ℝ)^8=256 by norm_num] at hp
    dsimp only [width]
    apply (div_le_iff₀ (pow_pos hlpos 8)).mpr
    linarith
  have hb := finite_reciprocal_weighted_sum S (X : ℝ) (width X) hXpos (width_positive X hX2) hwidth hS
  calc
    _ ≤ 512*constant*((Real.log (X : ℝ))^2+1)*(width X*(X : ℝ)+1) := hb
    _ = (X : ℝ)*scaledBound X := by dsimp only [scaledBound]; field_simp
    _ ≤ (X : ℝ)*ε := mul_le_mul_of_nonneg_left hh.1.le hXpos.le
    _ = _ := by ring

theorem width_tendsto : Tendsto width atTop (nhds 0) := by
  change Tendsto (fun X : ℕ ↦ 1/(Real.log (X : ℝ))^8) atTop (nhds 0)
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (tendsto_inv_atTop_zero.comp hlog).pow 8
  simpa only [one_div,inv_pow,Function.comp_def,zero_pow (by decide : (8 : ℕ) ≠ 0)] using hh
end PaperP1.LogarithmicGaussianSum





