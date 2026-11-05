module

public import PaperP1.Asymptotics.PolynomialConfinement
public import PaperP1.Arithmetic.ActivePhysicalPrimeGroups
public import PaperP1.Arithmetic.OffsetNonalignmentOn
public import PaperP1.Model.FiniteRademacher

/-! # Unconditionally few large actual prime groups

Every composite group is indexed once, even when different ternary supports
give the same two projected offsets. All restrictions of the relation code
share one threshold. No independence or regularization assumption is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActivePhysicalGroupCount

universe u

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ActivePhysicalPrimeGroups PaperP1.NormalizedUnitCount PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module

theorem uniform_count_active
    (C τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ 3 →
      ∀ X : ι → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ), L + 1 ≤ H →
      OffsetNonalignmentOn.NoExactOn X L (fun v ↦ label X L M v ≠ 0) →
        ((largeGroups X L M H ((N : ℝ) ^ τ)).card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨N₀, hN₀, h⟩ := PolynomialConfinement.companion_T8_1_little_o
    C τ (1 / 4) hτ (by norm_num) (by norm_num) 2 1 (by omega) (by omega)
    (ε / 9) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband ι _ _ hι X hX M H hH hno
  classical
  have hXpos (i : ι) : 1 ≤ X i := by
    have hi := (mem_Ico.mp (hX i)).1
    omega
  let S := largeGroups X L M H ((N : ℝ) ^ τ)
  have hdata (A : S) : ∃ v ∈ A.val, ∃ w ∈ A.val, v.1 ≠ w.1 :=
    support_two_blocks X L M H hXpos hH A.val (mem_filter.mp A.property).1
  choose v hv w hw hblocks using hdata
  have hactive (A : S) (z : ι × Fin (L + 1)) (hz : z ∈ A.val) : label X L M z ≠ 0 :=
    (group_support_data X L M H hXpos hH hι A.val (mem_filter.mp A.property).1).2.2.1 z hz
  let f : S → ι × ι := fun A ↦ ((v A).1, (w A).1)
  have hf (p : ι × ι) (A : S) (hA : A ∈ (univ : Finset S).filter fun A ↦ f A = p) :
      (v A).1 = p.1 ∧ (w A).1 = p.2 := by
    have he : f A = p := (mem_filter.mp hA).2
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  have hoff (a : Fin (L + 1)) : (offset a).natAbs ≤ 1 * (L + 1) := by
    have ha := EnlargedPairGeometry.offset_abs a
    rw [Int.abs_eq_natAbs] at ha
    have hnat : (offset a).natAbs ≤ L + 1 := by exact_mod_cast ha
    simpa only [one_mul] using hnat
  have hcount (p : ι × ι) :
      (((univ : Finset S).filter fun A ↦ f A = p).card : ℝ) ≤ (ε / 9) * ((L + 1 : ℕ) : ℝ) := by
    apply h N hN L hband S ((univ : Finset S).filter fun A ↦ f A = p)
      (fun A ↦ offset (v A).2) (fun A ↦ offset (w A).2) (fun A ↦ group X L M H A.val)
      (X p.1 : ℤ) (X p.2 : ℤ)
    · have hp := (mem_Ico.mp (hX p.1)).1
      have hz : (N : ℤ) ≤ (X p.1 : ℤ) := by exact_mod_cast hp
      norm_num only [Nat.cast_ofNat]
      omega
    · simpa only [Int.natAbs_natCast] using (mem_Ico.mp (hX p.1)).2.le
    · simpa only [Int.natAbs_natCast] using (mem_Ico.mp (hX p.2)).2.le
    · intro A _hA
      exact hoff _
    · intro A _hA
      exact hoff _
    · intro A _hA B _hB hAB
      exact group_coprime X L M H A.val B.val (fun he ↦ hAB (Subtype.ext he))
    · intro A hA
      have hd : ((group X L M H A.val : ℕ) : ℤ) ∣ (WindowPrimeIncidence.value X L (v A) : ℤ) := by
        exact_mod_cast group_dvd_value X L M H A.val (v A) (hv A)
      change ((group X L M H A.val : ℕ) : ℤ) ∣
        (startCompleteVertexLabel (X (v A).1) L (v A).2 : ℤ) at hd
      rw [label_cast (by have hx := hXpos (v A).1; omega), (hf p A hA).1] at hd
      exact hd
    · intro A hA
      have hd : ((group X L M H A.val : ℕ) : ℤ) ∣ (WindowPrimeIncidence.value X L (w A) : ℤ) := by
        exact_mod_cast group_dvd_value X L M H A.val (w A) (hw A)
      change ((group X L M H A.val : ℕ) : ℤ) ∣
        (startCompleteVertexLabel (X (w A).1) L (w A).2 : ℤ) at hd
      rw [label_cast (by have hx := hXpos (w A).1; omega), (hf p A hA).2] at hd
      exact hd
    · intro A _hA
      exact (mem_filter.mp A.property).2.le
    · intro A hA B hB hne
      exact hno p.1 p.2 (by
        intro he
        exact hblocks A ((hf p A hA).1.trans (he.trans (hf p A hA).2.symm)))
        (v A).2 (v B).2 (w A).2 (w B).2
        (by simpa only [← (hf p A hA).1] using hactive A (v A) (hv A))
        (by simpa only [← (hf p B hB).1] using hactive B (v B) (hv B))
        (by simpa only [← (hf p A hA).2] using hactive A (w A) (hw A))
        (by simpa only [← (hf p B hB).2] using hactive B (w B) (hw B)) hne
  have hcard : S.card = ∑ p : ι × ι, ((univ : Finset S).filter fun A ↦ f A = p).card := by
    simpa only [card_univ, Fintype.card_coe] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset S)) (t := (univ : Finset (ι × ι)))
        (f := f) (by intro A _hA; exact mem_univ _))
  have hιR : ((Fintype.card (ι × ι) : ℕ) : ℝ) ≤ 9 := by
    rw [Fintype.card_prod]
    have hsq : Fintype.card ι * Fintype.card ι ≤ 9 := by nlinarith
    exact_mod_cast hsq
  calc
    (S.card : ℝ) = ∑ p : ι × ι, (((univ : Finset S).filter fun A ↦ f A = p).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _p : ι × ι, (ε / 9) * ((L + 1 : ℕ) : ℝ) := sum_le_sum fun p _hp ↦ hcount p
    _ = ((Fintype.card (ι × ι) : ℕ) : ℝ) * ((ε / 9) * ((L + 1 : ℕ) : ℝ)) := by simp
    _ ≤ 9 * ((ε / 9) * ((L + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right hιR (by positivity)
    _ = ε * ((L + 1 : ℕ) : ℝ) := by ring

theorem uniform_count
    (C τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ 3 →
      ∀ X : ι → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      (∀ i j, i ≠ j → ActualOffsetNonalignment.NoExact (X i) (X j) L) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ), L + 1 ≤ H →
        ((largeGroups X L M H ((N : ℝ) ^ τ)).card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_count_active C τ ε hτ hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband ι _ _ hι X hX hno M H hH
  exact h N hN L hband ι hι X hX M H hH (OffsetNonalignmentOn.of_global X L _ hno)

end PaperP1.ActivePhysicalGroupCount
