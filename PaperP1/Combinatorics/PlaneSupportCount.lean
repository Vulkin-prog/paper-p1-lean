module

public import PaperP1.Combinatorics.PlaneFibreBounds
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp

/-! # A planar population with small line intersections has a small normal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneSupportCount

open Finset PaperP1.TripleCross PaperP1.PrimitiveTripleDirection
  PaperP1.PrimitivePlaneLines PaperP1.PlaneFibreBounds

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_bound (B : ℕ) (S : Finset (Fin 3 → ℤ)) (A : Fin 3 → ℤ) (h : ℤ) (M : ℝ)
    (hA : Primitive A) (hM : 0 ≤ M) (hplane : ∀ u ∈ S, dot A u = h)
    (hwidth : ∀ u ∈ S, ∀ v ∈ S, ∀ i, (u i - v i).natAbs ≤ B)
    (hline : ∀ a d : Fin 3 → ℤ, Primitive d →
      ((S.filter fun u ↦ ∃ t : ℤ, ∀ i, u i = a i + t * d i).card : ℝ) ≤ M) :
    (S.card : ℝ) ≤ M + 4 * (B : ℝ) ^ 2 / height A := by
  have hAp : (0 : ℝ) < height A := by exact_mod_cast height_pos A hA
  by_cases hcard : 1 < S.card
  · obtain ⟨d, hd, hdB, hAd⟩ := short_direction S A h hcard hplane hwidth
    obtain ⟨b, hb⟩ := (primitive_dot A).mp hA
    have hAb : dot A b = 1 := by rw [dot_comm]; exact hb
    obtain ⟨w, hw⟩ := (primitive_dot d).mp hd
    have hdp : (0 : ℝ) < height d := by exact_mod_cast height_pos d hd
    have hdBR : (height d : ℝ) ≤ B := by exact_mod_cast hdB
    let J := S.image (level d b)
    let T : ℝ := 2 * B * (height d : ℝ) / height A
    let Z : ℝ := (B : ℝ) / height d + 1
    have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
    have hlevels : (J.card : ℝ) ≤ T + 1 := level_card S A d b h hA hAb hAd hplane hwidth
    have hfibre (t : ℤ) : ((fibre S d b t).card : ℝ) ≤ Z :=
      fibre_card S A d b w h t hAb hd hAd hw hplane hwidth
    have hfibreM (t : ℤ) : ((fibre S d b t).card : ℝ) ≤ M := by
      by_cases hF : (fibre S d b t).Nonempty
      · obtain ⟨a, ha⟩ := hF
        have hsub : fibre S d b t ⊆ S.filter fun u ↦ ∃ k : ℤ, ∀ i, u i = a i + k * d i := by
          intro u hu
          refine mem_filter.mpr ⟨(mem_filter.mp hu).1, ?_⟩
          exact same_level_parameter A d b u a hAb hd hAd
            ((hplane u (mem_filter.mp hu).1).trans (hplane a (mem_filter.mp ha).1).symm)
            ((mem_filter.mp hu).2.trans (mem_filter.mp ha).2.symm)
        exact (show ((fibre S d b t).card : ℝ) ≤
          ((S.filter fun u ↦ ∃ k : ℤ, ∀ i, u i = a i + k * d i).card : ℝ) by
            exact_mod_cast card_le_card hsub).trans (hline a d hd)
      · rw [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero]
        exact hM
    obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < S.card)
    let t₀ := level d b u
    have ht₀ : t₀ ∈ J := mem_image.mpr ⟨u, hu, rfl⟩
    have hsum : (S.card : ℝ) = ∑ t ∈ J, ((fibre S d b t).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image (level d b) S
    have herase := sum_erase_add J (fun t ↦ ((fibre S d b t).card : ℝ)) ht₀
    have htail : (∑ t ∈ J.erase t₀, ((fibre S d b t).card : ℝ)) ≤ (J.erase t₀).card * Z := by
      calc
        _ ≤ ∑ _t ∈ J.erase t₀, Z := sum_le_sum (fun t _ ↦ hfibre t)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    have hJ : ((J.erase t₀).card : ℝ) ≤ T := by
      have hc : ((J.erase t₀).card : ℝ) + 1 = J.card := by exact_mod_cast card_erase_add_one ht₀
      linarith only [hlevels, hc]
    have htailT := mul_le_mul_of_nonneg_right hJ hZ
    have htotal : (S.card : ℝ) ≤ M + T * Z := by
      linarith only [hsum, herase, htail, htailT, hfibreM t₀]
    have hgeom : T * Z ≤ 4 * (B : ℝ) ^ 2 / height A := by
      have he : T * Z = 2 * B * ((B : ℝ) + height d) / height A := by
        dsimp only [T, Z]
        field_simp
      rw [he]
      apply div_le_div_of_nonneg_right _ hAp.le
      have hm := mul_le_mul_of_nonneg_left (show (B : ℝ) + height d ≤ 2 * B by linarith only [hdBR])
        (by positivity : (0 : ℝ) ≤ 2 * B)
      nlinarith only [hm]
    exact htotal.trans (by linarith only [hgeom])
  · by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      have hsmall : S.card ≤ 1 := by omega
      have hsub : S ⊆ S.filter fun u ↦ ∃ t : ℤ, ∀ i, u i = a i + t * A i := by
        intro u hu
        have hua := card_le_one.mp hsmall u hu a ha
        refine mem_filter.mpr ⟨hu, 0, ?_⟩
        intro i
        rw [hua]
        ring
      have htotal := (show (S.card : ℝ) ≤
        ((S.filter fun u ↦ ∃ t : ℤ, ∀ i, u i = a i + t * A i).card : ℝ) by
          exact_mod_cast card_le_card hsub).trans (hline a A hA)
      have hnon : 0 ≤ 4 * (B : ℝ) ^ 2 / height A := by positivity
      linarith only [htotal, hnon]
    · rw [not_nonempty_iff_eq_empty.mp hS, card_empty, Nat.cast_zero]
      positivity

end PaperP1.PlaneSupportCount
