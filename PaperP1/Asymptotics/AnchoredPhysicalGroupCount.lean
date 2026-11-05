module

public import PaperP1.Asymptotics.PolynomialConfinement
public import PaperP1.Arithmetic.AnchoredPhysicalPrimeGroups
public import PaperP1.Arithmetic.OffsetNonalignmentFrom
public import PaperP1.Model.FiniteRademacher

/-! # Few large prime groups at any fixed arity, using only anchor nonalignment

Different groups with the same projected offset pair retain their full
multiplicity in polynomial confinement. Source/source nonalignment is not needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredPhysicalGroupCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.PrimeCircuitSupports PaperP1.PrimeCircuitGroups PaperP1.AnchoredPhysicalPrimeGroups
  PaperP1.NormalizedUnitCount PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module

theorem uniform_count_active (s : ℕ) (hs : 1 ≤ s)
    (C τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ X : Option (Fin s) → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ) (hH : L + 1 ≤ H) (hXpos : ∀ i, 1 ≤ X i),
      OffsetNonalignmentFrom.NoExactFrom X L (fun v ↦ label X L M v ≠ 0) none →
        ((largeGroups X M H hXpos hH ((N : ℝ) ^ τ)).card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  obtain ⟨N₀, hN₀, h⟩ := PolynomialConfinement.companion_T8_1_little_o
    C τ (1 / 4) hτ (by norm_num) (by norm_num) 2 1 (by omega) (by omega)
    (ε / s) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband X hX M H hH hXpos hno
  classical
  let S := largeGroups X M H hXpos hH ((N : ℝ) ^ τ)
  have hdata (A : S) : ∃ u : Fin (L + 1), (none, u) ∈ A.val ∧
      ∃ a : Fin s, ∃ v : Fin (L + 1), (some a, v) ∈ A.val := by
    obtain ⟨u, hu, _hactive, _hpool, _hunique, a, v, hv⟩ :=
      group_target_source X M hXpos hH (mem_filter.mp A.property).1
    exact ⟨u, hu, a, v, hv⟩
  choose u hu b v hv using hdata
  have hactive (A : S) (w : Option (Fin s) × Fin (L + 1)) (hw : w ∈ A.val) :
      label X L M w ≠ 0 := group_active X M hXpos hH (mem_filter.mp A.property).1 w hw
  let f : S → Fin s := b
  have hf (a : Fin s) (A : S) (hA : A ∈ (univ : Finset S).filter fun A ↦ f A = a) : b A = a :=
    (mem_filter.mp hA).2
  have hoff (a : Fin (L + 1)) : (offset a).natAbs ≤ 1 * (L + 1) := by
    have ha := EnlargedPairGeometry.offset_abs a
    rw [Int.abs_eq_natAbs] at ha
    have hnat : (offset a).natAbs ≤ L + 1 := by exact_mod_cast ha
    simpa only [one_mul] using hnat
  have hcount (a : Fin s) :
      (((univ : Finset S).filter fun A ↦ f A = a).card : ℝ) ≤ (ε / s) * ((L + 1 : ℕ) : ℝ) := by
    apply h N hN L hband S ((univ : Finset S).filter fun A ↦ f A = a)
      (fun A ↦ offset (u A)) (fun A ↦ offset (v A)) (fun A ↦ groupValue X M H hXpos hH A.val)
      (X none : ℤ) (X (some a) : ℤ)
    · have hp := (mem_Ico.mp (hX none)).1
      have hz : (N : ℤ) ≤ (X none : ℤ) := by exact_mod_cast hp
      norm_num only [Nat.cast_ofNat]
      omega
    · simpa only [Int.natAbs_natCast] using (mem_Ico.mp (hX none)).2.le
    · simpa only [Int.natAbs_natCast] using (mem_Ico.mp (hX (some a))).2.le
    · intro A _hA
      exact hoff _
    · intro A _hA
      exact hoff _
    · intro A _hA B _hB hAB
      exact group_coprime X M hXpos hH (fun he ↦ hAB (Subtype.ext he))
    · intro A _hA
      have hd : ((groupValue X M H hXpos hH A.val : ℕ) : ℤ) ∣
          (WindowPrimeIncidence.value X L (none, u A) : ℤ) := by
        exact_mod_cast group_dvd_vertex X M hXpos hH A.val (hu A)
      change ((groupValue X M H hXpos hH A.val : ℕ) : ℤ) ∣
        (startCompleteVertexLabel (X none) L (u A) : ℤ) at hd
      rw [label_cast (by have hx := hXpos none; omega)] at hd
      exact hd
    · intro A hA
      have hd : ((groupValue X M H hXpos hH A.val : ℕ) : ℤ) ∣
          (WindowPrimeIncidence.value X L (some (b A), v A) : ℤ) := by
        exact_mod_cast group_dvd_vertex X M hXpos hH A.val (hv A)
      change ((groupValue X M H hXpos hH A.val : ℕ) : ℤ) ∣
        (startCompleteVertexLabel (X (some (b A))) L (v A) : ℤ) at hd
      rw [label_cast (by have hx := hXpos (some (b A)); omega), hf a A hA] at hd
      exact hd
    · intro A _hA
      exact (mem_filter.mp A.property).2.le
    · intro A hA B hB hne
      exact hno (some a) (by simp) (u A) (u B) (v A) (v B)
        (hactive A (none, u A) (hu A)) (hactive B (none, u B) (hu B))
        (by simpa only [← hf a A hA] using hactive A (some (b A), v A) (hv A))
        (by simpa only [← hf a B hB] using hactive B (some (b B), v B) (hv B)) hne
  have hcard : S.card = ∑ a : Fin s, ((univ : Finset S).filter fun A ↦ f A = a).card := by
    simpa only [card_univ, Fintype.card_coe] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset S)) (t := (univ : Finset (Fin s)))
        (f := f) (by intro A _hA; exact mem_univ _))
  calc
    (S.card : ℝ) = ∑ a : Fin s, (((univ : Finset S).filter fun A ↦ f A = a).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _a : Fin s, (ε / s) * ((L + 1 : ℕ) : ℝ) := sum_le_sum fun a _ha ↦ hcount a
    _ = (s : ℝ) * ((ε / s) * ((L + 1 : ℕ) : ℝ)) := by simp
    _ = ε * ((L + 1 : ℕ) : ℝ) := by field_simp

end PaperP1.AnchoredPhysicalGroupCount
