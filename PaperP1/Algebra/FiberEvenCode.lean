module

public import PaperP1.Algebra.FinitePiExtensionSupport

/-! # The canonical code of even selections in each equality fiber

No fiber is selected in the definition. If at most one fiber can repeat,
its full code has exactly that fiber's even-selection dimension.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiberEvenCode

open Finset

variable {K ι κ : Type*} [DivisionRing K] [Fintype ι]

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def constraint (f : ι → κ) (r : κ) : (ι → K) →ₗ[K] K :=
  Fintype.linearCombination K (fun i ↦ if f i = r then 1 else 0)

def code (f : ι → κ) : Submodule K (ι → K) := ⨅ r : κ, LinearMap.ker (constraint f r)

def fiber (f : ι → κ) (r : κ) : Finset ι := univ.filter fun i ↦ f i = r

theorem mem_fiber {f : ι → κ} {r : κ} {i : ι} : i ∈ fiber f r ↔ f i = r := by
  simp only [fiber, mem_filter, mem_univ, true_and]

theorem constraint_apply (f : ι → κ) (r : κ) (w : ι → K) :
    constraint f r w = ∑ i, if f i = r then w i else 0 := by
  simp only [constraint, Fintype.linearCombination_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem mem_code {f : ι → κ} {w : ι → K} : w ∈ code f ↔ ∀ r : κ, (∑ i, if f i = r then w i else 0) = 0 := by
  simp only [code, Submodule.mem_iInf, LinearMap.mem_ker, constraint_apply]

theorem zero_at_unique {f : ι → κ} {w : ι → K} (hw : w ∈ code f) (i : ι)
    (hi : ∀ j, f j = f i → j = i) : w i = 0 := by
  have hc := (mem_code.mp hw) (f i)
  have heq : (∑ j, if f j = f i then w j else 0) = w i := by
    rw [sum_eq_single i]
    · exact ite_eq_left rfl
    · intro j _ hji
      exact ite_eq_right (fun hj ↦ hji (hi j hj))
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  rw [heq] at hc
  exact hc

theorem code_eq_bot_of_injective {f : ι → κ} (hf : Function.Injective f) : code (K := K) f = ⊥ := by
  apply le_antisymm _ bot_le
  intro w hw
  change w = 0
  funext i
  exact zero_at_unique hw i (fun j hj ↦ hf hj)

theorem extension_mem (f : ι → κ) (r : κ)
    (w : LinearMap.ker (PaperP1.EvenSupportRank.sumMap K ↥(fiber f r))) :
    PaperP1.FinitePiExtension.extend (Function.Embedding.subtype (fun i ↦ i ∈ fiber f r)) w.val ∈ code f := by
  let e : ↥(fiber f r) ↪ ι := Function.Embedding.subtype (fun i ↦ i ∈ fiber f r)
  have hout (i : ι) (hi : i ∉ fiber f r) : PaperP1.FinitePiExtension.extend e w.val i = 0 := by
    apply PaperP1.FinitePiExtensionSupport.extend_zero_outside
    intro j hj
    exact hi (hj ▸ j.property)
  apply mem_code.mpr
  intro c
  by_cases hcr : c = r
  · subst c
    have heq : (∑ i, if f i = r then PaperP1.FinitePiExtension.extend e w.val i else 0) =
        ∑ i, PaperP1.FinitePiExtension.extend e w.val i := by
      apply sum_congr rfl
      intro i _
      by_cases hi : f i = r
      · exact ite_eq_left hi
      · rw [ite_eq_right hi, hout i (by simpa only [fiber, mem_filter, mem_univ, true_and] using hi)]
    rw [heq, PaperP1.FinitePiExtension.sum_extend]
    exact (PaperP1.EvenSupportRank.sumMap_apply w.val).symm.trans w.property
  · apply sum_eq_zero
    intro i _
    by_cases hi : f i = c
    · rw [ite_eq_left hi]
      exact hout i (by
        intro hmem
        have hir := (mem_filter.mp hmem).2
        exact hcr (hi.symm.trans hir))
    · exact ite_eq_right hi

theorem fiber_rank_le (f : ι → κ) (r : κ) :
    (fiber f r).card - 1 ≤ Module.finrank K (code (K := K) f) := by
  let e : ↥(fiber f r) ↪ ι := Function.Embedding.subtype (fun i ↦ i ∈ fiber f r)
  let g : LinearMap.ker (PaperP1.EvenSupportRank.sumMap K ↥(fiber f r)) →ₗ[K] code (K := K) f :=
    { toFun := fun w ↦ ⟨PaperP1.FinitePiExtension.extend e w.val, extension_mem f r w⟩
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (map_smul _ _ _) }
  have hg : Function.Injective g := by
    intro u v heq
    apply Subtype.ext
    exact PaperP1.FinitePiExtensionSupport.extend_injective e (congrArg Subtype.val heq)
  have hd := LinearMap.finrank_le_finrank_of_injective hg
  simpa only [PaperP1.EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] using hd

theorem finrank_eq_fiber {f : ι → κ} (r : κ)
    (hunique : ∀ i, f i ≠ r → ∀ j, f j = f i → j = i) :
    Module.finrank K (code (K := K) f) = (fiber f r).card - 1 := by
  apply Nat.le_antisymm _ (fiber_rank_le f r)
  have hout (w : code (K := K) f) (i : ι) (hi : i ∉ fiber f r) : w.val i = 0 := by
    have hir : f i ≠ r := by simpa only [fiber, mem_filter, mem_univ, true_and] using hi
    exact zero_at_unique w.property i (hunique i hir)
  apply PaperP1.EvenSupportRank.finrank_le_of_supported_even (code (K := K) f).subtype Subtype.val_injective (fiber f r) hout
  intro w
  have hc := (mem_code.mp w.property) r
  have heq : (∑ i, if f i = r then w.val i else 0) = ∑ i, w.val i := by
    apply sum_congr rfl
    intro i _
    by_cases hi : f i = r
    · exact ite_eq_left hi
    · rw [ite_eq_right hi, hout w i (by simpa only [fiber, mem_filter, mem_univ, true_and] using hi)]
  exact heq.symm.trans hc

end PaperP1.FiberEvenCode
