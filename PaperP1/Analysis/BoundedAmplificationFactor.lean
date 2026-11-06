module

public import PaperP1.Analysis.AmplifiedPrimeProductMean

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.BoundedAmplificationFactor
open PaperP1

def span : ℝ := 2*Real.exp 3

def constant : ℝ := Real.exp 1*(Real.sqrt Real.pi*span+2*Real.pi*span^2)

theorem span_pos : 0 < span := by unfold span; positivity

theorem constant_pos : 0 < constant := by unfold constant; have := span_pos; positivity

theorem real_factor_bound (L M T B : ℝ) (hL : 0 < L) (hM : 0 ≤ M) (hspan : M ≤ span*L)
    (hT : 0 ≤ T) (hB : 0 ≤ B) :
    Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*M)*(M/L^2*B) ≤ constant*(T/L+1)*B := by
  have hr0 : 0 ≤ M/L := div_nonneg hM hL.le
  have hr : M/L ≤ span := (div_le_iff₀ hL).mpr hspan
  have hs := (sq_le_sq₀ hr0 span_pos.le).mpr hr
  have ht : 0 ≤ T/L := div_nonneg hT hL.le
  have hscalar : Real.sqrt Real.pi*(T/L)*(M/L)+2*Real.pi*(M/L)^2 ≤
      (Real.sqrt Real.pi*span+2*Real.pi*span^2)*(T/L+1) := by
    calc
      _ ≤ Real.sqrt Real.pi*(T/L)*span+2*Real.pi*span^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hr (mul_nonneg (Real.sqrt_nonneg Real.pi) ht))
          (mul_le_mul_of_nonneg_left hs (by positivity))
      _ ≤ _ := by
        have h1 := mul_nonneg (Real.sqrt_nonneg Real.pi) span_pos.le
        have h2 : 0 ≤ 2*Real.pi*span^2 := by positivity
        nlinarith only [h1,h2,mul_nonneg h2 ht]
  calc
    _ = Real.exp 1*(Real.sqrt Real.pi*(T/L)*(M/L)+2*Real.pi*(M/L)^2)*B := by
      field_simp [hL.ne']
    _ ≤ Real.exp 1*((Real.sqrt Real.pi*span+2*Real.pi*span^2)*(T/L+1))*B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar (Real.exp_pos 1).le) hB
    _ = _ := by unfold constant; ring

theorem sampled_factor_bound (L M T B d : ℝ) (hL : 0 < L) (hM : 0 ≤ M) (hspan : M ≤ span*L)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hd : 0 ≤ d) (hd4 : d ≤ 4) :
    Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*M)*(2+d^2)*(M/L^2*B) ≤
      18*constant*((T+1)/L+1)*B := by
  have hfactor : 2+d^2 ≤ 18 := by nlinarith only [hd,hd4]
  have hbase : 0 ≤ Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*M)*(M/L^2*B) := by positivity
  calc
    _ = (2+d^2)*(Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*M)*(M/L^2*B)) := by ring
    _ ≤ 18*(Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*M)*(M/L^2*B)) :=
      mul_le_mul_of_nonneg_right hfactor hbase
    _ ≤ 18*(constant*((T+1)/L+1)*B) := mul_le_mul_of_nonneg_left
      (real_factor_bound L M (T+1) B hL hM hspan (by linarith) hB) (by norm_num)
    _ = _ := by ring
end PaperP1.BoundedAmplificationFactor
