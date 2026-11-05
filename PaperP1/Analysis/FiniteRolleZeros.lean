module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Finset.Sort

/-! # Finite zero populations and repeated Rolle inequalities

The derivative zeros are constructed between consecutive actual zeros.
No finiteness or cardinality claim about a whole analytic zero set is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRolleZeros

open Finset Set

theorem exists_derivative_zeros (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioo a b)) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ f x = 0) :
    ∃ T : Finset ℝ, (∀ x ∈ T, x ∈ Ioo a b ∧ deriv f x = 0) ∧ S.card ≤ T.card + 1 := by
  classical
  by_cases hempty : S.card = 0
  · exact ⟨∅, by simp, by simp [hempty]⟩
  let n := S.card - 1
  have hn : S.card = n + 1 := by dsimp only [n]; omega
  let e : Fin (n + 1) ↪o ℝ := S.orderEmbOfFin hn
  have he (i : Fin (n + 1)) : e i ∈ Ioo a b ∧ f (e i) = 0 :=
    hS _ (S.orderEmbOfFin_mem hn i)
  have hgap (i : Fin n) : ∃ c ∈ Ioo (e i.castSucc) (e i.succ), deriv f c = 0 := by
    apply exists_deriv_eq_zero (e.strictMono (by simp))
    · apply hf.mono
      intro x hx
      exact ⟨lt_of_lt_of_le (he i.castSucc).1.1 hx.1,
        lt_of_le_of_lt hx.2 (he i.succ).1.2⟩
    · rw [(he i.castSucc).2, (he i.succ).2]
  choose g hg hzero using hgap
  have hgmono : StrictMono g := by
    intro i j hij
    have hidx : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    exact (hg i).2.trans_le (e.monotone hidx) |>.trans (hg j).1
  refine ⟨univ.image g, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hx
    exact ⟨⟨(he i.castSucc).1.1.trans (hg i).1,
      (hg i).2.trans (he i.succ).1.2⟩, hzero i⟩
  · rw [card_image_of_injective _ hgmono.injective, card_univ, Fintype.card_fin]
    omega

theorem card_le_of_derivative_bound (a b : ℝ) (f : ℝ → ℝ) (k : ℕ)
    (hf : ContinuousOn f (Ioo a b))
    (hder : ∀ T : Finset ℝ, (∀ x ∈ T, x ∈ Ioo a b ∧ deriv f x = 0) → T.card ≤ k)
    (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ f x = 0) : S.card ≤ k + 1 := by
  obtain ⟨T, hT, hcard⟩ := exists_derivative_zeros a b f hf S hS
  exact hcard.trans (Nat.add_le_add_right (hder T hT) 1)

theorem card_le_of_iterated_derivative_nonzero (a b : ℝ) (n : ℕ) (f : ℝ → ℝ)
    (hcont : ∀ j ≤ n, ContinuousOn (iteratedDeriv j f) (Ioo a b))
    (hnon : ∀ x ∈ Ioo a b, iteratedDeriv n f x ≠ 0)
    (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ f x = 0) : S.card ≤ n := by
  induction n generalizing f S with
  | zero =>
    have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hnon x (hS x hx).1 (by simpa only [iteratedDeriv_zero] using (hS x hx).2)
    simp [hempty]
  | succ n ih =>
    apply card_le_of_derivative_bound a b f n (by simpa only [iteratedDeriv_zero] using hcont 0 (by omega))
    · intro T hT
      apply ih (deriv f) _ _ T hT
      · intro j hj
        simpa only [iteratedDeriv_succ'] using hcont (j + 1) (by omega)
      · intro x hx
        simpa only [iteratedDeriv_succ'] using hnon x hx
    · exact hS

end PaperP1.FiniteRolleZeros
