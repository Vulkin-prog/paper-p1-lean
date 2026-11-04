module

public import PaperP1.Arithmetic.TwoKernelDeterminantBoxes

/-! # Exact primitive reduction of both pairs in the variable-coefficient equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantPrimitiveReduction

open Finset PaperP1.TwoKernelDeterminantBoxes

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def scale (a : Quad) : ℕ := (Nat.gcd a.1.1 a.1.2) ^ 2 * Nat.gcd a.2.1 a.2.2

def reduced (a : Quad) : Quad :=
  ((a.1.1 / Nat.gcd a.1.1 a.1.2, a.1.2 / Nat.gcd a.1.1 a.1.2),
    (a.2.1 / Nat.gcd a.2.1 a.2.2, a.2.2 / Nat.gcd a.2.1 a.2.2))

def reductions (h : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 h) ×ˢ (Icc 1 h)).filter fun gq ↦ gq.1 ^ 2 * gq.2 ∣ h

theorem reconstruct (a : Quad) :
    Nat.gcd a.1.1 a.1.2 * (reduced a).1.1 = a.1.1 ∧
      Nat.gcd a.1.1 a.1.2 * (reduced a).1.2 = a.1.2 ∧
        Nat.gcd a.2.1 a.2.2 * (reduced a).2.1 = a.2.1 ∧
          Nat.gcd a.2.1 a.2.2 * (reduced a).2.2 = a.2.2 :=
  ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _), Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _), Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)⟩

theorem left_factor (c : ℕ) (a : Quad) :
    c * a.1.1 ^ 2 * a.2.1 = scale a * (c * (reduced a).1.1 ^ 2 * (reduced a).2.1) := by
  obtain ⟨hd, _, hu, _⟩ := reconstruct a
  calc
    _ = c * (Nat.gcd a.1.1 a.1.2 * (reduced a).1.1) ^ 2 *
        (Nat.gcd a.2.1 a.2.2 * (reduced a).2.1) := by rw [hd, hu]
    _ = _ := by unfold scale; ring

theorem right_factor (c : ℕ) (a : Quad) :
    c * a.1.2 ^ 2 * a.2.2 = scale a * (c * (reduced a).1.2 ^ 2 * (reduced a).2.2) := by
  obtain ⟨_, he, _, hv⟩ := reconstruct a
  calc
    _ = c * (Nat.gcd a.1.1 a.1.2 * (reduced a).1.2) ^ 2 *
        (Nat.gcd a.2.1 a.2.2 * (reduced a).2.2) := by rw [he, hv]
    _ = _ := by unfold scale; ring

theorem scale_divides {a : Quad} {c₁ c₂ h : ℕ}
    (heq : c₁ * a.1.1 ^ 2 * a.2.1 + h = c₂ * a.1.2 ^ 2 * a.2.2) : scale a ∣ h := by
  have h₁ : scale a ∣ c₁ * a.1.1 ^ 2 * a.2.1 := ⟨_, left_factor c₁ a⟩
  have h₂ : scale a ∣ c₂ * a.1.2 ^ 2 * a.2.2 := ⟨_, right_factor c₂ a⟩
  have hh : h = c₂ * a.1.2 ^ 2 * a.2.2 - c₁ * a.1.1 ^ 2 * a.2.1 := by omega
  rw [hh]
  exact Nat.dvd_sub h₂ h₁

theorem primitive (a : Quad) (hd : 0 < a.1.1) (he : 0 < a.1.2)
    (hu : 0 < a.2.1) (hv : 0 < a.2.2) :
    0 < scale a ∧ 0 < (reduced a).1.1 ∧ 0 < (reduced a).1.2 ∧
      0 < (reduced a).2.1 ∧ 0 < (reduced a).2.2 ∧
        (reduced a).1.1.Coprime (reduced a).1.2 ∧ (reduced a).2.1.Coprime (reduced a).2.2 := by
  have hg : 0 < Nat.gcd a.1.1 a.1.2 := Nat.gcd_pos_of_pos_left _ hd
  have hq : 0 < Nat.gcd a.2.1 a.2.2 := Nat.gcd_pos_of_pos_left _ hu
  refine ⟨mul_pos (pow_pos hg _) hq, Nat.div_pos (Nat.gcd_le_left _ hd) hg,
    Nat.div_pos (Nat.gcd_le_right _ he) hg, Nat.div_pos (Nat.gcd_le_left _ hu) hq,
    Nat.div_pos (Nat.gcd_le_right _ hv) hq, Nat.coprime_div_gcd_div_gcd hg,
    Nat.coprime_div_gcd_div_gcd hq⟩

theorem reduced_equation {a : Quad} {c₁ c₂ h : ℕ}
    (hs : 0 < scale a)
    (heq : c₁ * a.1.1 ^ 2 * a.2.1 + h = c₂ * a.1.2 ^ 2 * a.2.2) :
    c₁ * (reduced a).1.1 ^ 2 * (reduced a).2.1 + h / scale a =
      c₂ * (reduced a).1.2 ^ 2 * (reduced a).2.2 := by
  apply mul_left_cancel₀ hs.ne'
  rw [mul_add, Nat.mul_div_cancel' (scale_divides heq), ← left_factor, ← right_factor]
  exact heq

theorem reduced_shift_bounds {a : Quad} {c₁ c₂ h : ℕ} (hs : 0 < scale a) (hh : 0 < h)
    (heq : c₁ * a.1.1 ^ 2 * a.2.1 + h = c₂ * a.1.2 ^ 2 * a.2.2) :
    0 < h / scale a ∧ h / scale a ≤ h ∧ scale a ≤ h := by
  have hle := Nat.le_of_dvd hh (scale_divides heq)
  exact ⟨Nat.div_pos hle hs, Nat.div_le_self _ _, hle⟩

theorem reductions_card (h : ℕ) : (reductions h).card ≤ h ^ 2 := by
  calc
    _ ≤ ((Icc 1 h) ×ˢ (Icc 1 h)).card := card_filter_le _ _
    _ = _ := by simp only [card_product, Nat.card_Icc, Nat.add_sub_cancel]; ring

theorem actual_reduction_mem {a : Quad} {c₁ c₂ h : ℕ}
    (hd : 0 < a.1.1) (hu : 0 < a.2.1) (hh : 0 < h)
    (heq : c₁ * a.1.1 ^ 2 * a.2.1 + h = c₂ * a.1.2 ^ 2 * a.2.2) :
    (Nat.gcd a.1.1 a.1.2, Nat.gcd a.2.1 a.2.2) ∈ reductions h := by
  have hg : 0 < Nat.gcd a.1.1 a.1.2 := Nat.gcd_pos_of_pos_left _ hd
  have hq : 0 < Nat.gcd a.2.1 a.2.2 := Nat.gcd_pos_of_pos_left _ hu
  have hs : scale a ≤ h := Nat.le_of_dvd hh (scale_divides heq)
  have hgs : Nat.gcd a.1.1 a.1.2 ≤ scale a := by
    have hg2 : Nat.gcd a.1.1 a.1.2 ≤ (Nat.gcd a.1.1 a.1.2) ^ 2 := by nlinarith only [hg]
    exact hg2.trans (Nat.le_mul_of_pos_right _ hq)
  have hqs : Nat.gcd a.2.1 a.2.2 ≤ scale a :=
    Nat.le_mul_of_pos_left _ (pow_pos hg _)
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Icc.mpr ⟨hg, hgs.trans hs⟩, mem_Icc.mpr ⟨hq, hqs.trans hs⟩⟩, scale_divides heq⟩

theorem reduced_injective_on (g q : ℕ) :
    Set.InjOn reduced {a : Quad | Nat.gcd a.1.1 a.1.2 = g ∧ Nat.gcd a.2.1 a.2.2 = q} := by
  intro a ha b hb heq
  have ha' : g * (reduced a).1.1 = a.1.1 ∧ g * (reduced a).1.2 = a.1.2 ∧
      q * (reduced a).2.1 = a.2.1 ∧ q * (reduced a).2.2 = a.2.2 := by
    simpa only [ha.1, ha.2] using reconstruct a
  have hb' : g * (reduced b).1.1 = b.1.1 ∧ g * (reduced b).1.2 = b.1.2 ∧
      q * (reduced b).2.1 = b.2.1 ∧ q * (reduced b).2.2 = b.2.2 := by
    simpa only [hb.1, hb.2] using reconstruct b
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · exact ha'.1.symm.trans ((congrArg (fun r : Quad ↦ g * r.1.1) heq).trans hb'.1)
  · exact ha'.2.1.symm.trans ((congrArg (fun r : Quad ↦ g * r.1.2) heq).trans hb'.2.1)
  · exact ha'.2.2.1.symm.trans ((congrArg (fun r : Quad ↦ q * r.2.1) heq).trans hb'.2.2.1)
  · exact ha'.2.2.2.symm.trans ((congrArg (fun r : Quad ↦ q * r.2.2) heq).trans hb'.2.2.2)

theorem finite_primitive_cover {c₁ c₂ h : ℕ} (hh : 0 < h) (S : Finset Quad)
    (hS : ∀ a ∈ S, 0 < a.1.1 ∧ 0 < a.2.1 ∧
      c₁ * a.1.1 ^ 2 * a.2.1 + h = c₂ * a.1.2 ^ 2 * a.2.2) :
    S.card ≤ ∑ gq ∈ reductions h,
      (((S.filter fun a ↦ (Nat.gcd a.1.1 a.1.2, Nat.gcd a.2.1 a.2.2) = gq).image reduced).card) := by
  let F := fun gq : ℕ × ℕ ↦ S.filter fun a ↦
    (Nat.gcd a.1.1 a.1.2, Nat.gcd a.2.1 a.2.2) = gq
  have hsub : S ⊆ (reductions h).biUnion F := by
    intro a ha
    have hd := hS a ha
    exact mem_biUnion.mpr ⟨_, actual_reduction_mem hd.1 hd.2.1 hh hd.2.2,
      mem_filter.mpr ⟨ha, rfl⟩⟩
  have hinj (gq : ℕ × ℕ) : Set.InjOn reduced (↑(F gq) : Set Quad) := by
    apply (reduced_injective_on gq.1 gq.2).mono
    intro a ha
    have he := (mem_filter.mp ha).2
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  calc
    _ ≤ ((reductions h).biUnion F).card := card_le_card hsub
    _ ≤ ∑ gq ∈ reductions h, (F gq).card := card_biUnion_le
    _ = _ := by
      apply sum_congr rfl
      intro gq _
      exact (card_image_of_injOn (hinj gq)).symm

end PaperP1.DeterminantPrimitiveReduction
