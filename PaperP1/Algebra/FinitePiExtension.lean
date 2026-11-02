module

public import PaperP1.Algebra.EvenImage
public import Mathlib.LinearAlgebra.Pi

/-! # Extension by zero along finite embeddings preserves sums and actual value combinations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePiExtension

open Finset

variable {K ι κ : Type*} [DivisionRing K] [Fintype ι] [Fintype κ]

local instance : DecidableEq κ := Classical.decEq _

def extend (e : ι ↪ κ) : (ι → K) →ₗ[K] (κ → K) :=
  ∑ i : ι, (LinearMap.single K (fun _ : κ ↦ K) (e i)).comp (LinearMap.proj i)

omit [Fintype κ] in
theorem extend_apply (e : ι ↪ κ) (w : ι → K) :
    extend e w = ∑ i : ι, Pi.single (e i) (w i) := by
  simp only [extend, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.single_apply, LinearMap.proj_apply]

omit [Fintype κ] in
theorem extend_at (e : ι ↪ κ) (w : ι → K) (i : ι) : extend e w (e i) = w i := by
  classical
  rw [extend_apply, Finset.sum_apply]
  change (∑ j : ι, (Pi.single (e j) (w j) : κ → K) (e i)) = w i
  rw [sum_eq_single i]
  · simp
  · intro j _ hji
    simp [e.injective.ne hji]
  · simp

theorem sum_extend (e : ι ↪ κ) (w : ι → K) : (∑ j : κ, extend e w j) = ∑ i : ι, w i := by
  rw [extend_apply]
  simp only [Finset.sum_apply]
  rw [sum_comm]
  simp only [Fintype.sum_pi_single']

variable {E : Type*} [AddCommGroup E] [Module K E]

theorem combination_extend (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i) (w : ι → K) :
    EvenImage.combination g (extend e w) = EvenImage.combination f w := by
  rw [extend_apply, map_sum, EvenImage.combination_apply]
  apply sum_congr rfl
  intro i _
  simp only [EvenImage.combination, Fintype.linearCombination_apply_single, hfg]

def extendEven (e : ι ↪ κ) :
    LinearMap.ker (EvenSupportRank.sumMap K ι) →ₗ[K] LinearMap.ker (EvenSupportRank.sumMap K κ) where
  toFun w := ⟨extend e w.val, by
    rw [LinearMap.mem_ker, EvenSupportRank.sumMap_apply, sum_extend]
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem extendEven_injective (e : ι ↪ κ) : Function.Injective (extendEven (K := K) e) := by
  intro u v hh
  apply Subtype.ext
  funext i
  have heq : extend e u.val = extend e v.val := congrArg Subtype.val hh
  have hpoint := congrFun heq (e i)
  simpa only [extend_at] using hpoint

theorem evenMap_extend (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i)
    (w : LinearMap.ker (EvenSupportRank.sumMap K ι)) :
    EvenImage.evenMap g (extendEven e w) = EvenImage.evenMap f w := by
  exact combination_extend e f g hfg w.val

theorem even_injective_of_embedding (e : ι ↪ κ) (f : ι → E) (g : κ → E) (hfg : ∀ i, g (e i) = f i)
    (hg : Function.Injective (EvenImage.evenMap (K := K) g)) : Function.Injective (EvenImage.evenMap (K := K) f) := by
  intro u v hh
  apply extendEven_injective e
  apply hg
  rw [evenMap_extend e f g hfg, evenMap_extend e f g hfg]
  exact hh

end PaperP1.FinitePiExtension
