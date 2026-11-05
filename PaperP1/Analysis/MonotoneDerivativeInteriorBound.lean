module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith

/-! # Quantitative interior bounds from a monotone first derivative

Two actual mean-value secants bound a central derivative from both sides.
No second derivative bound or fixed derivative sign is required as an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonotoneDerivativeInteriorBound

open Set

theorem secant_bound (f : ℝ → ℝ) (a b M : ℝ) (hab : a < b)
    (ha : |f a| ≤ M) (hb : |f b| ≤ M) :
    |(f b - f a) / (b - a)| ≤ 2 * M / (b - a) := by
  rw [abs_div, abs_of_pos (sub_pos.mpr hab)]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hab.le)
  exact (abs_sub (f b) (f a)).trans (by linarith)

theorem central_bound (f : ℝ → ℝ) (c h M : ℝ) (hh : 0 < h)
    (hc : ContinuousOn f (Icc (c - h) (c + h)))
    (hd : DifferentiableOn ℝ f (Ioo (c - h) (c + h)))
    (hbound : ∀ x ∈ Icc (c - h) (c + h), |f x| ≤ M)
    (hmono : MonotoneOn (deriv f) (Icc (c - h) (c + h)) ∨
      AntitoneOn (deriv f) (Icc (c - h) (c + h))) :
    |deriv f c| ≤ 2 * M / h := by
  have hleft : c - h < c := by linarith
  have hright : c < c + h := by linarith
  have hsubL : Icc (c - h) c ⊆ Icc (c - h) (c + h) := fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
  have hsubR : Icc c (c + h) ⊆ Icc (c - h) (c + h) := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  have hsubLo : Ioo (c - h) c ⊆ Ioo (c - h) (c + h) := fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
  have hsubRo : Ioo c (c + h) ⊆ Ioo (c - h) (c + h) := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨l, hl, heL⟩ := exists_deriv_eq_slope f hleft (hc.mono hsubL) (hd.mono hsubLo)
  obtain ⟨u, hu, heR⟩ := exists_deriv_eq_slope f hright (hc.mono hsubR) (hd.mono hsubRo)
  have hcenter : c ∈ Icc (c - h) (c + h) := ⟨hleft.le, hright.le⟩
  have hLo : c - h ∈ Icc (c - h) (c + h) := ⟨le_rfl, by linarith⟩
  have hHi : c + h ∈ Icc (c - h) (c + h) := ⟨by linarith, le_rfl⟩
  have hlc : l ∈ Icc (c - h) (c + h) := hsubL (Ioo_subset_Icc_self hl)
  have huc : u ∈ Icc (c - h) (c + h) := hsubR (Ioo_subset_Icc_self hu)
  have hL : |deriv f l| ≤ 2 * M / h := by
    rw [heL]
    have hs := secant_bound f (c - h) c M hleft (hbound _ hLo) (hbound _ hcenter)
    simpa only [show c - (c - h) = h by ring] using hs
  have hR : |deriv f u| ≤ 2 * M / h := by
    rw [heR]
    have hs := secant_bound f c (c + h) M hright (hbound _ hcenter) (hbound _ hHi)
    simpa only [show c + h - c = h by ring] using hs
  apply abs_le.mpr
  rcases hmono with hm | hm
  · exact ⟨(abs_le.mp hL).1.trans (hm hlc hcenter hl.2.le),
      (hm hcenter huc hu.1.le).trans (abs_le.mp hR).2⟩
  · exact ⟨(abs_le.mp hR).1.trans (hm hcenter huc hu.1.le),
      (hm hlc hcenter hl.2.le).trans (abs_le.mp hL).2⟩

theorem central_bound_on_open (f : ℝ → ℝ) (a b c h M : ℝ) (hh : 0 < h)
    (hd : DifferentiableOn ℝ f (Ioo a b))
    (hsub : Icc (c - h) (c + h) ⊆ Ioo a b)
    (hbound : ∀ x ∈ Icc (c - h) (c + h), |f x| ≤ M)
    (hmono : MonotoneOn (deriv f) (Ioo a b) ∨ AntitoneOn (deriv f) (Ioo a b)) :
    |deriv f c| ≤ 2 * M / h := by
  apply central_bound f c h M hh (hd.continuousOn.mono hsub)
    (hd.mono (fun x hx ↦ hsub (Ioo_subset_Icc_self hx))) hbound
  rcases hmono with hm | hm
  · exact Or.inl (hm.mono hsub)
  · exact Or.inr (hm.mono hsub)

end PaperP1.MonotoneDerivativeInteriorBound
