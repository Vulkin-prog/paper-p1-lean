module

public import PaperP1.Algebra.PrimitivePlaneLines
public import PaperP1.Combinatorics.IntegerDiameter
public import Mathlib.Tactic.Positivity

/-! # Integer level and fibre counts inside a plane meeting a bounded cube -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneFibreBounds

open Finset PaperP1.TripleCross PaperP1.PrimitiveTripleDirection PaperP1.PrimitivePlaneLines

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def fibre (S : Finset (Fin 3 → ℤ)) (d b : Fin 3 → ℤ) (t : ℤ) : Finset (Fin 3 → ℤ) :=
  S.filter fun u ↦ level d b u = t

theorem abs_cast (z : ℤ) : |(z : ℝ)| = (z.natAbs : ℝ) := by
  rw [← Int.cast_abs]
  simpa only [Int.cast_natCast] using congrArg (fun w : ℤ ↦ (w : ℝ)) (Int.abs_eq_natAbs z)

theorem parameter_difference (A d b w u v : Fin 3 → ℤ) (hb : dot A b = 1)
    (hd : Primitive d) (hAd : dot A d = 0) (hw : dot w d = 1)
    (huv : dot A u = dot A v) (hl : level d b u = level d b v) :
    ∀ i, u i - v i = (dot w u - dot w v) * d i := by
  obtain ⟨t, ht⟩ := same_level_parameter A d b u v hb hd hAd huv hl
  have hparam : dot w u = dot w v + t * dot w d := by
    simp only [dot, ht]
    ring
  rw [hw, mul_one] at hparam
  intro i
  rw [ht i]
  have he : dot w u - dot w v = t := by linarith only [hparam]
  rw [he]
  ring

theorem level_diameter {B : ℕ} (S : Finset (Fin 3 → ℤ)) (A d b : Fin 3 → ℤ) (h : ℤ)
    (hA : Primitive A) (hb : dot A b = 1) (hd : dot A d = 0)
    (hplane : ∀ u ∈ S, dot A u = h)
    (hwidth : ∀ u ∈ S, ∀ v ∈ S, ∀ i, (u i - v i).natAbs ≤ B) :
    ∀ u ∈ S, ∀ v ∈ S, |((level d b u - level d b v : ℤ) : ℝ)| ≤
      2 * B * (height d : ℝ) / height A := by
  intro u hu v hv
  obtain ⟨j, hj⟩ := height_attained A
  have hcross := difference_cross A d b u v hb hd ((hplane u hu).trans (hplane v hv).symm)
  have heq := congrArg Int.natAbs (congrFun hcross j)
  simp only [Int.natAbs_mul, hj] at heq
  have hbound := cross_coordinate_natAbs_le d (u - v) (height d) B
    (coordinate_natAbs_le_height d) (hwidth u hu v hv) j
  rw [heq] at hbound
  have hR : ((level d b u - level d b v).natAbs : ℝ) * height A ≤ 2 * (height d : ℝ) * B := by
    exact_mod_cast hbound
  have hAp : (0 : ℝ) < height A := by exact_mod_cast height_pos A hA
  apply (le_div_iff₀ hAp).mpr
  rw [abs_cast]
  nlinarith only [hR]

theorem level_card {B : ℕ} (S : Finset (Fin 3 → ℤ)) (A d b : Fin 3 → ℤ) (h : ℤ)
    (hA : Primitive A) (hb : dot A b = 1) (hd : dot A d = 0)
    (hplane : ∀ u ∈ S, dot A u = h)
    (hwidth : ∀ u ∈ S, ∀ v ∈ S, ∀ i, (u i - v i).natAbs ≤ B) :
    ((S.image (level d b)).card : ℝ) ≤ 2 * B * (height d : ℝ) / height A + 1 := by
  apply IntegerDiameter.card_le (S.image (level d b)) _ (by positivity)
  intro a ha c hc
  obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hc
  exact level_diameter S A d b h hA hb hd hplane hwidth u hu v hv

theorem fibre_card {B : ℕ} (S : Finset (Fin 3 → ℤ)) (A d b w : Fin 3 → ℤ) (h t : ℤ)
    (hb : dot A b = 1) (hd : Primitive d) (hAd : dot A d = 0) (hw : dot w d = 1)
    (hplane : ∀ u ∈ S, dot A u = h)
    (hwidth : ∀ u ∈ S, ∀ v ∈ S, ∀ i, (u i - v i).natAbs ≤ B) :
    ((fibre S d b t).card : ℝ) ≤ (B : ℝ) / height d + 1 := by
  have hpair (u : Fin 3 → ℤ) (hu : u ∈ fibre S d b t) (v : Fin 3 → ℤ) (hv : v ∈ fibre S d b t) :=
    parameter_difference A d b w u v hb hd hAd hw
      ((hplane u (mem_filter.mp hu).1).trans (hplane v (mem_filter.mp hv).1).symm)
      ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
  apply IntegerDiameter.image_card_le (fibre S d b t) (dot w) _ (by positivity)
  · intro u hu v hv heq
    funext i
    have hh := hpair u hu v hv i
    rw [heq, sub_self, zero_mul] at hh
    exact sub_eq_zero.mp hh
  · intro u hu v hv
    obtain ⟨j, hj⟩ := height_attained d
    have hh := congrArg Int.natAbs (hpair u hu v hv j)
    simp only [Int.natAbs_mul, hj] at hh
    have hwidthj := hwidth u (mem_filter.mp hu).1 v (mem_filter.mp hv).1 j
    rw [hh] at hwidthj
    have hR : ((dot w u - dot w v).natAbs : ℝ) * height d ≤ B := by exact_mod_cast hwidthj
    have hdp : (0 : ℝ) < height d := by exact_mod_cast height_pos d hd
    apply (le_div_iff₀ hdp).mpr
    rw [abs_cast]
    exact hR

end PaperP1.PlaneFibreBounds
