module

public import PaperP1.Probability.OrderedTuples
public import PaperP1.Probability.StoppedFiniteLaw
public import Mathlib.Data.Nat.Factorial.BigOperators

/-! # Falling factorials count the ordered active tuples exactly -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Probability

open Finset

theorem cast_descFactorial_eq_falling_product (n r : ℕ) :
    (n.descFactorial r : ℝ) = ∏ i ∈ range r, ((n : ℝ) - i) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  by_cases h : r ≤ n
  · apply prod_congr rfl
    intro i hi
    exact Nat.cast_sub ((Nat.le_of_lt (mem_range.mp hi)).trans h)
  · have hnr : n < r := Nat.lt_of_not_ge h
    have hleft : (∏ i ∈ range r, ((n - i : ℕ) : ℝ)) = 0 :=
      prod_eq_zero (mem_range.mpr hnr) (by simp)
    have hright : (∏ i ∈ range r, ((n : ℝ) - i)) = 0 :=
      prod_eq_zero (mem_range.mpr hnr) (sub_self _)
    exact hleft.trans hright.symm

variable {Ω ι : Type*} [DecidableEq ι]

def activeSites (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : Finset ι :=
  G.filter fun x ↦ J x ω = true

omit [DecidableEq ι] in
theorem card_activeSites (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    (activeSites G J ω).card = indicatorCount G J ω := by
  rw [activeSites, card_filter]
  unfold indicatorCount
  apply sum_congr rfl
  intro x _
  cases J x ω <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false,
    Bool.toNat_true]

def activeTupleEquiv (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    {t : OrderedTuple G r // ∀ i, J (t i).val ω = true} ≃
      OrderedTuple (activeSites G J ω) r where
  toFun t :=
    { toFun := fun i ↦ ⟨(t.val i).val, mem_filter.mpr ⟨(t.val i).property, t.property i⟩⟩
      inj' := by
        intro i j hij
        exact t.val.injective
          (Subtype.ext (congrArg (fun z : activeSites G J ω ↦ z.val) hij)) }
  invFun t :=
    ⟨{ toFun := fun i ↦ ⟨(t i).val, (mem_filter.mp (t i).property).1⟩
       inj' := by
         intro i j hij
         exact t.injective (Subtype.ext (congrArg (fun z : G ↦ z.val) hij)) },
      fun i ↦ (mem_filter.mp (t i).property).2⟩
  left_inv t := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv t := by
    apply Function.Embedding.ext
    intro i
    rfl

omit [DecidableEq ι] in
theorem card_activeTuples (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    Fintype.card {t : OrderedTuple G r // ∀ i, J (t i).val ω = true} =
      (indicatorCount G J ω).descFactorial r := by
  classical
  rw [Fintype.card_congr (activeTupleEquiv G J ω r), Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_coe, card_activeSites]

omit [DecidableEq ι] in
theorem sum_active_tuple_indicators (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    (∑ t : OrderedTuple G r, if ∀ i, J (t i).val ω = true then (1 : ℝ) else 0) =
      ((indicatorCount G J ω).descFactorial r : ℝ) := by
  classical
  rw [← card_activeTuples G J ω r, Fintype.card_subtype]
  exact sum_boole _ _

theorem sum_tuple_products_eq_descFactorial
    (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    (∑ t : OrderedTuple G r, ∏ x ∈ tupleValues t, (indicatorValue (J x ω) : ℝ)) =
      ((indicatorCount G J ω).descFactorial r : ℝ) := by
  calc
    _ = ∑ t : OrderedTuple G r, if ∀ i, J (t i).val ω = true then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro t _
      rw [indicator_product_eq_indicator]
      simp only [tupleValues_forall t (fun x ↦ J x ω = true)]
    _ = _ := sum_active_tuple_indicators G J ω r

end PaperP1.Probability
