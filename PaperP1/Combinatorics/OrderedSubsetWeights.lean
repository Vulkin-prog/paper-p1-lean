module

public import PaperP1.Probability.OrderedTuples
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Every unordered r-set has exactly r! ordered distinct enumerations, with arbitrary weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderedSubsetWeights

open Finset PaperP1.Probability

variable {ι : Type*} [DecidableEq ι]

local instance orderedSubsetWeightsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def fiberEquiv (G I : Finset ι) (r : ℕ) (hIG : I ⊆ G) (hI : I.card = r) :
    {t : OrderedTuple G r // tupleValues t = I} ≃ (Fin r ↪ I) where
  toFun t :=
    { toFun := fun i ↦ ⟨(t.val i).val, by
        exact Eq.mp (congrArg (fun J : Finset ι ↦ (t.val i).val ∈ J) t.property)
          ((mem_tupleValues t.val _).mpr ⟨i, rfl⟩)⟩
      inj' := by
        intro i j h
        apply t.val.injective
        exact Subtype.ext (congrArg (fun x : I ↦ x.val) h) }
  invFun b := by
    let t : OrderedTuple G r :=
      { toFun := fun i ↦ ⟨(b i).val, hIG (b i).property⟩
        inj' := by
          intro i j h
          apply b.injective
          exact Subtype.ext (congrArg (fun x : G ↦ x.val) h) }
    have hsub : tupleValues t ⊆ I := by
      intro x hx
      obtain ⟨i, rfl⟩ := (mem_tupleValues t x).mp hx
      exact (b i).property
    exact ⟨t, eq_of_subset_of_card_le hsub (by rw [tupleValues_card, hI])⟩
  left_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv b := by
    apply Function.Embedding.ext
    intro i
    rfl

theorem fiber_card (G I : Finset ι) (r : ℕ) (hIG : I ⊆ G) (hI : I.card = r) :
    Fintype.card {t : OrderedTuple G r // tupleValues t = I} = r.factorial := by
  rw [Fintype.card_congr (fiberEquiv G I r hIG hI), Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_coe, hI, Nat.descFactorial_self]

def population (G : Finset ι) (r : ℕ) (F : Finset (Finset ι)) : Finset (OrderedTuple G r) :=
  univ.filter (fun t ↦ tupleValues t ∈ F)

theorem fiber_sum (G I : Finset ι) (r : ℕ) (hIG : I ⊆ G) (hI : I.card = r) (a : ℝ) :
    (∑ t : OrderedTuple G r, if tupleValues t = I then a else 0) = (r.factorial : ℝ) * a := by
  rw [← sum_filter]
  rw [sum_const, nsmul_eq_mul]
  congr 1
  have hcard := Fintype.card_subtype (fun t : OrderedTuple G r ↦ tupleValues t = I)
  rw [fiber_card G I r hIG hI] at hcard
  exact_mod_cast hcard.symm

theorem weighted_sum (G : Finset ι) (r : ℕ) (F : Finset (Finset ι))
    (hF : F ⊆ G.powersetCard r) (w : Finset ι → ℝ) :
    (∑ t ∈ population G r F, w (tupleValues t)) = (r.factorial : ℝ) * ∑ I ∈ F, w I := by
  unfold population
  rw [sum_filter]
  have hswap : (∑ t : OrderedTuple G r, if tupleValues t ∈ F then w (tupleValues t) else 0) =
      ∑ t : OrderedTuple G r, ∑ I ∈ F, if tupleValues t = I then w I else 0 := by
    apply sum_congr rfl
    intro t _
    simp only [sum_ite_eq]
  rw [hswap, sum_comm, mul_sum]
  apply sum_congr rfl
  intro I hI
  obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (hF hI)
  exact fiber_sum G I r hIG hcard (w I)

end PaperP1.OrderedSubsetWeights
