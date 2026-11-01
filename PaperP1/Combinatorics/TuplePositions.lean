module

public import PaperP1.Combinatorics.TupleExtensions
public import PaperP1.Combinatorics.GraphStarWeights
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Perm

/-! # Finite permutation covers put an actual seed at arbitrary tuple positions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TuplePositions

open Finset PaperP1.TupleExtensions

def permute {r : ℕ} (e : Equiv.Perm (Fin r)) (x : Fin r → ℕ) : Fin r → ℕ := x ∘ e

def allPositions {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) (k : ℕ) :
    Finset (Fin (s + k) → ℕ) :=
  univ.biUnion fun e : Equiv.Perm (Fin (s + k)) ↦ (distinctMore G F k).image (permute e)

theorem initial_apply {s : ℕ} (k : ℕ) (y : Fin (s + k) → ℕ) (i : Fin s) :
    initial k y i = y (Fin.castAdd k i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [initial, ih]
    rfl

theorem permute_injective {r : ℕ} (e : Equiv.Perm (Fin r)) : Function.Injective (permute e) := by
  intro x y hxy
  funext i
  have h := congrFun hxy (e.symm i)
  simpa only [permute, Function.comp_apply, Equiv.apply_symm_apply] using h

theorem of_reindexed {s k : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ))
    (y : Fin (s + k) → ℕ) (e : Equiv.Perm (Fin (s + k)))
    (hy : permute e y ∈ distinctMore G F k) : y ∈ allPositions G F k := by
  apply mem_biUnion.mpr
  refine ⟨e.symm, mem_univ _, mem_image.mpr ⟨permute e y, hy, ?_⟩⟩
  funext i
  simp only [permute, Function.comp_apply, Equiv.apply_symm_apply]

theorem of_injected_seed {s k : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ))
    (hF : ∀ x ∈ F, ∀ i, x i ∈ G) (y : Fin (s + k) → ℕ)
    (hy : ∀ i, y i ∈ G) (hinj : Function.Injective y)
    (f : Fin s → Fin (s + k)) (hf : Function.Injective f)
    (hseed : (fun i ↦ y (f i)) ∈ F) : y ∈ allPositions G F k := by
  have hcanonical : Function.Injective (Fin.castAdd k : Fin s → Fin (s + k)) := by
    intro i j hij
    exact Fin.ext (congrArg (fun a : Fin (s + k) ↦ a.val) hij)
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) f hcanonical hf
  apply of_reindexed G F y e
  apply (mem_distinctMore G F hF k _).mpr
  refine ⟨?_, fun i ↦ hy (e i), hinj.comp e.injective⟩
  have hinit : initial k (permute e y) = fun i ↦ y (f i) := by
    funext i
    rw [initial_apply]
    change y (e (Fin.castAdd k i)) = y (f i)
    rw [he]
  rwa [hinit]

theorem mass_bound {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) (k : ℕ)
    (w : (Fin (s + k) → ℕ) → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hinvariant : ∀ (e : Equiv.Perm (Fin (s + k))) y, w (permute e y) = w y) :
    (∑ y ∈ allPositions G F k, w y) ≤ ((s + k).factorial : ℝ) * ∑ y ∈ distinctMore G F k, w y := by
  calc
    _ ≤ ∑ e : Equiv.Perm (Fin (s + k)), ∑ y ∈ (distinctMore G F k).image (permute e), w y :=
      GraphStarWeights.sum_biUnion_le_nonneg univ _ w hw
    _ = ∑ _e : Equiv.Perm (Fin (s + k)), ∑ y ∈ distinctMore G F k, w y := by
      apply sum_congr rfl
      intro e _
      rw [sum_image (permute_injective e).injOn]
      exact sum_congr rfl (fun y _ ↦ hinvariant e y)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end PaperP1.TuplePositions
