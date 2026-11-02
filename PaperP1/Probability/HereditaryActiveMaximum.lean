module

public import PaperP1.Probability.SubsetFactorials
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith

/-! # The maximum active member of a hereditary finite family

Every subset of a maximizing active family is still admissible and active.
This gives an all-order factorial counting bound before any probability or
arithmetic estimate is applied.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HereditaryActiveMaximum

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*}

local instance hereditaryActiveMaximumDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def Hereditary (F : Finset (Finset ι)) : Prop := ∀ A ∈ F, ∀ B ⊆ A, B ∈ F

def activeFamilies (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) : Finset (Finset ι) :=
  F.filter fun A ↦ ∀ x ∈ A, J x ω = true

def maximumSize (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  (activeFamilies F J ω).sup Finset.card

def orderFamilies (F : Finset (Finset ι)) (r : ℕ) : Finset (Finset ι) :=
  F.filter fun A ↦ A.card = r

theorem active_mem {F : Finset (Finset ι)} {J : ι → Ω → Bool} {ω : Ω} {A : Finset ι} :
    A ∈ activeFamilies F J ω ↔ A ∈ F ∧ ∀ x ∈ A, J x ω = true := mem_filter

theorem active_hereditary (F : Finset (Finset ι)) (hF : Hereditary F)
    (J : ι → Ω → Bool) (ω : Ω) : Hereditary (activeFamilies F J ω) := by
  intro A hA B hBA
  obtain ⟨hAF, hactive⟩ := active_mem.mp hA
  exact active_mem.mpr ⟨hF A hAF B hBA, fun x hx ↦ hactive x (hBA hx)⟩

theorem maximum_congr {Ψ : Type*} (F : Finset (Finset ι))
    (J : ι → Ω → Bool) (K : ι → Ψ → Bool) (ω : Ω) (σ : Ψ)
    (heq : ∀ A ∈ F, ∀ x ∈ A, J x ω = K x σ) : maximumSize F J ω = maximumSize F K σ := by
  unfold maximumSize
  congr 1
  ext A
  rw [active_mem, active_mem]
  constructor
  · rintro ⟨hA, hJ⟩
    exact ⟨hA, fun x hx ↦ (heq A hA x hx).symm.trans (hJ x hx)⟩
  · rintro ⟨hA, hK⟩
    exact ⟨hA, fun x hx ↦ (heq A hA x hx).trans (hK x hx)⟩

theorem maximum_attained (F : Finset (Finset ι)) (hzero : ∅ ∈ F)
    (J : ι → Ω → Bool) (ω : Ω) :
    ∃ A ∈ activeFamilies F J ω, maximumSize F J ω = A.card := by
  have hne : (activeFamilies F J ω).Nonempty := ⟨∅, active_mem.mpr ⟨hzero, by simp⟩⟩
  exact exists_mem_eq_sup (activeFamilies F J ω) hne Finset.card

theorem maximum_le_ground (G : Finset ι) (F : Finset (Finset ι))
    (hF : ∀ A ∈ F, A ⊆ G) (J : ι → Ω → Bool) (ω : Ω) : maximumSize F J ω ≤ G.card := by
  apply Finset.sup_le
  intro A hA
  exact card_le_card (hF A (active_mem.mp hA).1)

theorem maximum_le_count (G : Finset ι) (F : Finset (Finset ι))
    (hF : ∀ A ∈ F, A ⊆ G) (J : ι → Ω → Bool) (ω : Ω) :
    maximumSize F J ω ≤ indicatorCount G J ω := by
  classical
  rw [← card_activeSites]
  apply Finset.sup_le
  intro A hA
  obtain ⟨hAF, hactive⟩ := active_mem.mp hA
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨hF A hAF hx, hactive x hx⟩

theorem choose_le_active_count (F : Finset (Finset ι)) (hzero : ∅ ∈ F) (hF : Hereditary F)
    (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    (maximumSize F J ω).choose r ≤ (orderFamilies (activeFamilies F J ω) r).card := by
  classical
  obtain ⟨A, hA, hmax⟩ := maximum_attained F hzero J ω
  rw [hmax, ← card_powersetCard r A]
  apply card_le_card
  intro B hB
  obtain ⟨hBA, hcard⟩ := mem_powersetCard.mp hB
  exact mem_filter.mpr ⟨active_hereditary F hF J ω A hA B hBA, hcard⟩

theorem sum_active_products (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    (∑ A ∈ orderFamilies F r, ∏ x ∈ A, (indicatorValue (J x ω) : ℝ)) =
      ((orderFamilies (activeFamilies F J ω) r).card : ℝ) := by
  simp_rw [indicator_product_eq_indicator]
  rw [sum_boole]
  congr 1
  congr 1
  ext A
  simp only [orderFamilies, activeFamilies, mem_filter]
  tauto

theorem choose_bound (F : Finset (Finset ι)) (hzero : ∅ ∈ F) (hF : Hereditary F)
    (J : ι → Ω → Bool) (ω : Ω) (r : ℕ) :
    ((maximumSize F J ω).choose r : ℝ) ≤
      ∑ A ∈ orderFamilies F r, ∏ x ∈ A, (indicatorValue (J x ω) : ℝ) := by
  rw [sum_active_products]
  exact_mod_cast choose_le_active_count F hzero hF J ω r

theorem expected_choose_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (F : Finset (Finset ι)) (hzero : ∅ ∈ F) (hF : Hereditary F)
    (J : ι → Ω → Bool) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).choose r : ℝ)) ≤
      ∑ A ∈ orderFamilies F r, finiteJointMoment P J A := by
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦
        ∑ A ∈ orderFamilies F r, ∏ x ∈ A, (indicatorValue (J x ω) : ℝ)) :=
      sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (choose_bound F hzero hF J ω r) (P.weight_nonneg ω)
    _ = _ := finiteExpectation_sum _ _ _

theorem expected_choose_binomial_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ℝ) (hp : 0 ≤ p)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ p ^ A.card) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).choose r : ℝ)) ≤
      (G.card.choose r : ℝ) * p ^ r := by
  classical
  have hsub : orderFamilies F r ⊆ G.powersetCard r := by
    intro A hA
    obtain ⟨hAF, hcard⟩ := mem_filter.mp hA
    exact mem_powersetCard.mpr ⟨hground A hAF, hcard⟩
  calc
    _ ≤ ∑ A ∈ orderFamilies F r, finiteJointMoment P J A := expected_choose_bound P F hzero hF J r
    _ ≤ ∑ _A ∈ orderFamilies F r, p ^ r := by
      apply sum_le_sum
      intro A hA
      obtain ⟨hAF, hcard⟩ := mem_filter.mp hA
      simpa only [hcard] using hjoint A hAF
    _ = ((orderFamilies F r).card : ℝ) * p ^ r := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (G.card.choose r : ℝ) * p ^ r := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp r)
      exact_mod_cast (card_le_card hsub).trans_eq (card_powersetCard r G)

theorem expected_factorial_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ℝ) (hp : 0 ≤ p)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ p ^ A.card) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).descFactorial r : ℝ)) ≤
      ((G.card : ℝ) * p) ^ r := by
  have hchoose := expected_choose_binomial_bound P G F hzero hF hground J p hp hjoint r
  have hfactor : (r.factorial : ℝ) * (G.card.choose r : ℝ) ≤ (G.card : ℝ) ^ r := by
    have h := Nat.descFactorial_le_pow G.card r
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h
    exact_mod_cast h
  have hid (ω : Ω) : ((maximumSize F J ω).descFactorial r : ℝ) =
      (r.factorial : ℝ) * ((maximumSize F J ω).choose r : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp_rw [hid]
  rw [finiteExpectation_const_mul]
  calc
    _ ≤ (r.factorial : ℝ) * ((G.card.choose r : ℝ) * p ^ r) :=
      mul_le_mul_of_nonneg_left hchoose (Nat.cast_nonneg r.factorial)
    _ ≤ (G.card : ℝ) ^ r * p ^ r := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfactor (pow_nonneg hp r)
    _ = _ := (mul_pow _ _ _).symm

theorem power_le_active_generator (F : Finset (Finset ι)) (hzero : ∅ ∈ F) (hF : Hereditary F)
    (J : ι → Ω → Bool) (ω : Ω) (s : ℝ) (hs : 1 ≤ s) :
    s ^ maximumSize F J ω ≤
      ∑ A ∈ F, (s - 1) ^ A.card * ∏ x ∈ A, (indicatorValue (J x ω) : ℝ) := by
  classical
  obtain ⟨D, hD, hmax⟩ := maximum_attained F hzero J ω
  have hsub : D.powerset ⊆ activeFamilies F J ω := by
    intro A hA
    exact active_hereditary F hF J ω D hD A (mem_powerset.mp hA)
  have hid : s ^ D.card = ∑ A ∈ D.powerset, (s - 1) ^ A.card := by
    have h := prod_one_add (f := fun _ : ι ↦ s - 1) D
    simpa only [prod_const, show 1 + (s - 1) = s by ring] using h
  rw [hmax, hid]
  calc
    _ ≤ ∑ A ∈ activeFamilies F J ω, (s - 1) ^ A.card :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ pow_nonneg (sub_nonneg.mpr hs) _)
    _ = _ := by
      unfold activeFamilies
      rw [sum_filter]
      apply sum_congr rfl
      intro A _
      rw [indicator_product_eq_indicator]
      split_ifs <;> simp

theorem expected_power_binomial_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ℝ) (hp : 0 ≤ p)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ p ^ A.card) (s : ℝ) (hs : 1 ≤ s) :
    finiteExpectation P.weight (fun ω ↦ s ^ maximumSize F J ω) ≤
      (1 + p * (s - 1)) ^ G.card := by
  classical
  have hsub : F ⊆ G.powerset := fun A hA ↦ mem_powerset.mpr (hground A hA)
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦
        ∑ A ∈ F, (s - 1) ^ A.card * ∏ x ∈ A, (indicatorValue (J x ω) : ℝ)) :=
      sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (power_le_active_generator F hzero hF J ω s hs) (P.weight_nonneg ω)
    _ = ∑ A ∈ F, (s - 1) ^ A.card * finiteJointMoment P J A := by
      rw [finiteExpectation_sum]
      apply sum_congr rfl
      intro A _
      exact finiteExpectation_const_mul _ _ _
    _ ≤ ∑ A ∈ F, (p * (s - 1)) ^ A.card := by
      apply sum_le_sum
      intro A hA
      simpa only [mul_pow, mul_comm] using mul_le_mul_of_nonneg_left (hjoint A hA) (pow_nonneg (sub_nonneg.mpr hs) _)
    _ ≤ ∑ A ∈ G.powerset, (p * (s - 1)) ^ A.card :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ pow_nonneg (mul_nonneg hp (sub_nonneg.mpr hs)) _)
    _ = _ := by
      have h := prod_one_add (f := fun _ : ι ↦ p * (s - 1)) G
      simpa only [prod_const] using h.symm

theorem expected_choose_poisson_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ℝ) (hp : 0 ≤ p)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ p ^ A.card) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).choose r : ℝ)) ≤
      ((G.card : ℝ) * p) ^ r / (r.factorial : ℝ) := by
  have hf := expected_factorial_bound P G F hzero hF hground J p hp hjoint r
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul] at hf
  rw [finiteExpectation_const_mul] at hf
  apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos r : (0 : ℝ) < r.factorial)).mpr
  simpa only [mul_comm] using hf

theorem expected_power_exponential_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ℝ) (hp : 0 ≤ p)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ p ^ A.card) (s : ℝ) (hs : 1 ≤ s) :
    finiteExpectation P.weight (fun ω ↦ s ^ maximumSize F J ω) ≤
      Real.exp ((s - 1) * ((G.card : ℝ) * p)) := by
  calc
    _ ≤ (1 + p * (s - 1)) ^ G.card := expected_power_binomial_bound P G F hzero hF hground J p hp hjoint s hs
    _ ≤ (Real.exp (p * (s - 1))) ^ G.card := by
      apply pow_le_pow_left₀ (by nlinarith only [mul_nonneg hp (sub_nonneg.mpr hs)])
      linarith only [Real.add_one_le_exp (p * (s - 1))]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem tail_bound [Fintype Ω] [LinearOrder ι]
    (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ℝ) (hp : 0 ≤ p)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ p ^ A.card) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ if r ≤ maximumSize F J ω then (1 : ℝ) else 0) ≤
      ((G.card : ℝ) * p) ^ r / (r.factorial : ℝ) := by
  apply (le_trans ?_ (expected_choose_poisson_bound P G F hzero hF hground J p hp hjoint r))
  apply sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (P.weight_nonneg ω)
  dsimp only
  split_ifs with h
  · have hpos := Nat.choose_pos h
    exact_mod_cast (show 1 ≤ (maximumSize F J ω).choose r by omega)
  · exact Nat.cast_nonneg _

end PaperP1.HereditaryActiveMaximum
