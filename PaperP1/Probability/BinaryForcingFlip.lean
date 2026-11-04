module

public import PaperP1.Model.AnchoredPrivateForcing
public import PaperP1.Probability.FiniteCoupling

/-! # Exact positive flip costs and the two-candidate orientation balance

No fairness assumption is imposed on the chosen orientation in the balance
lemma. Fairness is needed only for the parity of the two original source
bits, which is proved internally on the independent uniform word cube.
The arithmetic clean-pair construction is a separate obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryForcingFlip

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.UniformFubini PaperP1.Arithmetic

local instance binaryForcingFlipDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def bitIndicator (z : F₂) : ℝ := if z = 1 then 1 else 0

def ones (z : F₂) : ℕ := if z = 1 then 1 else 0

theorem bitIndicator_eq_cast (z : F₂) : bitIndicator z = (ones z : ℝ) := by
  by_cases h : z = 1 <;> simp [bitIndicator, ones, h]

theorem indicator_add_one (z : F₂) : bitIndicator (z + 1) = 1 - bitIndicator z := by
  have h : ones (z + 1) + ones z = 1 := by revert z; decide
  have hr : bitIndicator (z + 1) + bitIndicator z = 1 := by
    simpa only [bitIndicator_eq_cast, Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ ↦ (n : ℝ)) h
  linarith

theorem orientation_pointwise (x y b c ξ : F₂) :
    bitIndicator (x + y + b + c) ≤
      bitIndicator (x + b + ξ) + bitIndicator (y + c + ξ) := by
  have h : ones (x + y + b + c) ≤ ones (x + b + ξ) + ones (y + c + ξ) := by
    revert x y b c ξ
    decide
  simp only [bitIndicator_eq_cast]
  exact_mod_cast h

theorem uniform_parity_fair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hji : j ≠ i) (c : F₂) :
    average (fun u : ι → F₂ ↦ bitIndicator (u i + u j + c)) = 1 / 2 := by
  let f := fun u : ι → F₂ ↦ bitIndicator (u i + u j + c)
  let e := Equiv.addRight (Pi.single i (1 : F₂) : ι → F₂)
  have he (u : ι → F₂) : f (e u) = 1 - f u := by
    change bitIndicator ((u + (Pi.single i (1 : F₂) : ι → F₂)) i +
      (u + (Pi.single i (1 : F₂) : ι → F₂)) j + c) = _
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hji, add_zero]
    rw [show (u i + 1) + u j + c = (u i + u j + c) + 1 by abel, indicator_add_one]
  have htranslation := UniformFubini.equiv e f
  have hmean : average (fun u ↦ f (e u)) = 1 - average f := by
    rw [show (fun u ↦ f (e u)) = (fun u ↦ 1 - f u) from funext he]
    rw [average, finiteExpectation_sub, finiteExpectation_const,
      (uniformFiniteProbability (ι → F₂)).total_weight, one_mul]
  change average f = 1 / 2
  linarith only [htranslation, hmean]

theorem uniform_single_fair {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (b : F₂) :
    average (fun u : ι → F₂ ↦ bitIndicator (u i - b)) = 1 / 2 := by
  let f := fun u : ι → F₂ ↦ bitIndicator (u i - b)
  let e := Equiv.addRight (Pi.single i (1 : F₂) : ι → F₂)
  have he (u : ι → F₂) : f (e u) = 1 - f u := by
    change bitIndicator ((u + (Pi.single i (1 : F₂) : ι → F₂)) i - b) = _
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [show (u i + 1) - b = (u i - b) + 1 by abel, indicator_add_one]
  have htranslation := UniformFubini.equiv e f
  have hmean : average (fun u ↦ f (e u)) = 1 - average f := by
    rw [show (fun u ↦ f (e u)) = (fun u ↦ 1 - f u) from funext he]
    rw [average, finiteExpectation_sub, finiteExpectation_const,
      (uniformFiniteProbability (ι → F₂)).total_weight, one_mul]
  change average f = 1 / 2
  linarith only [htranslation, hmean]

theorem anchored_change_bit (x y b c : F₂) : x - (b + (y - c)) = x + y + b + c := by
  revert x y b c
  decide

theorem anchored_uniform_flip_fair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i anchor : ι) (hne : anchor ≠ i) (b : ι → F₂) :
    average (fun u : ι → F₂ ↦
      bitIndicator (u i - (b i + (u anchor - b anchor)))) = 1 / 2 := by
  simp_rw [anchored_change_bit]
  simpa only [add_assoc] using uniform_parity_fair i anchor hne (b i + b anchor)

theorem two_candidate_balance {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω)
    (X Y ξ : Ω → F₂) (b c : F₂)
    (hfair : finiteExpectation P.weight (fun ω ↦ bitIndicator (X ω + Y ω + b + c)) = 1 / 2) :
    1 / 2 ≤ finiteExpectation P.weight (fun ω ↦ bitIndicator (X ω + b + ξ ω)) +
      finiteExpectation P.weight (fun ω ↦ bitIndicator (Y ω + c + ξ ω)) := by
  have h := finiteExpectation_mono P (fun ω ↦ orientation_pointwise (X ω) (Y ω) b c (ξ ω))
  rw [hfair, finiteExpectation_add] at h
  exact h

/-- Some forced candidate flips with probability at least1/4, for ANY orientation. -/
theorem one_candidate_quarter {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω)
    (X Y ξ : Ω → F₂) (b c : F₂)
    (hfair : finiteExpectation P.weight (fun ω ↦ bitIndicator (X ω + Y ω + b + c)) = 1 / 2) :
    (1 / 4 ≤ finiteExpectation P.weight (fun ω ↦ bitIndicator (X ω + b + ξ ω))) ∨
      (1 / 4 ≤ finiteExpectation P.weight (fun ω ↦ bitIndicator (Y ω + c + ξ ω))) := by
  have h := two_candidate_balance P X Y ξ b c hfair
  by_cases hi : 1 / 4 ≤ finiteExpectation P.weight (fun ω ↦ bitIndicator (X ω + b + ξ ω))
  · exact Or.inl hi
  · exact Or.inr (by linarith)

theorem disjoint_flip_cost {V : Type*} [Fintype V] [Nonempty V]
    (T : V ≃ V) (A : V → Prop) [DecidablePred A] (hdisjoint : ∀ v, A v → ¬A (T v)) :
    average (fun v ↦ |(if A v then (1 : ℝ) else 0) - (if A (T v) then 1 else 0)|) =
      2 * average (fun v ↦ if A v then (1 : ℝ) else 0) := by
  have hp (v : V) : |(if A v then (1 : ℝ) else 0) - (if A (T v) then 1 else 0)| =
      (if A v then 1 else 0) + (if A (T v) then 1 else 0) := by
    by_cases h : A v
    · have hn := hdisjoint v h
      simp only [h, hn, ite_true, ite_false, sub_zero, abs_one, add_zero]
    · by_cases hh : A (T v) <;> norm_num [h, hh]
  rw [show (fun v ↦ |(if A v then (1 : ℝ) else 0) - (if A (T v) then 1 else 0)|) =
    (fun v ↦ (if A v then 1 else 0) + (if A (T v) then 1 else 0)) from funext hp]
  rw [average, finiteExpectation_add]
  change average (fun v ↦ if A v then (1 : ℝ) else 0) +
    average (fun v ↦ if A (T v) then (1 : ℝ) else 0) = _
  rw [UniformFubini.equiv T (fun v ↦ if A v then (1 : ℝ) else 0)]
  ring

theorem independent_flip_cost {Ω V : Type*} [Fintype Ω] [Fintype V] [Nonempty V]
    (P : FiniteProbability Ω) (δ : Ω → F₂) (T : V ≃ V) (A : V → Prop) [DecidablePred A]
    (hdisjoint : ∀ v, A v → ¬A (T v)) :
    finiteExpectation P.weight (fun ω ↦ average (fun v ↦
      |(if A v then (1 : ℝ) else 0) - (if A (if δ ω = 1 then T v else v) then 1 else 0)|)) =
        2 * finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω)) *
          average (fun v ↦ if A v then (1 : ℝ) else 0) := by
  have hp (ω : Ω) : average (fun v ↦
      |(if A v then (1 : ℝ) else 0) - (if A (if δ ω = 1 then T v else v) then 1 else 0)|) =
      bitIndicator (δ ω) * (2 * average (fun v ↦ if A v then (1 : ℝ) else 0)) := by
    by_cases h : δ ω = 1
    · simpa only [h, ite_true, bitIndicator, one_mul] using disjoint_flip_cost T A hdisjoint
    · simp only [h, ite_false, sub_self, abs_zero, constant, bitIndicator, zero_mul]
  simp_rw [hp]
  rw [finiteExpectation_mul_const]
  ring

def orbit {ι : Type*} (b u : ι → F₂) : Prop := ∃ s : F₂, u = fun i ↦ b i + s

theorem orbit_disjoint_single_flip {ι : Type*} [DecidableEq ι]
    (b : ι → F₂) (i j : ι) (hji : j ≠ i) (u : ι → F₂) (hu : orbit b u) :
    ¬orbit b (u + Pi.single i 1) := by
  rintro ⟨t, ht⟩
  obtain ⟨s, rfl⟩ := hu
  have hj := congrFun ht j
  change (b j + s) + (Pi.single i (1 : F₂) : ι → F₂) j = b j + t at hj
  simp only [Pi.single_eq_of_ne hji, add_zero] at hj
  have hst := add_left_cancel hj
  have hi := congrFun ht i
  change (b i + s) + (Pi.single i (1 : F₂) : ι → F₂) i = b i + t at hi
  rw [Pi.single_eq_same, ← hst] at hi
  have hz : (1 : F₂) = 0 := add_left_cancel (by simpa only [add_zero] using hi)
  exact one_ne_zero hz

end PaperP1.BinaryForcingFlip
