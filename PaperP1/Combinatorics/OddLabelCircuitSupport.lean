module

public import PaperP1.Coding.RegularizedSupportPools
public import PaperP1.Combinatorics.LabelClassPartition
public import PaperP1.Combinatorics.TwoFreeBlockSupport

/-! # An odd occurrence of a whole binary label class has a bounded circuit support through a fixed source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OddLabelCircuitSupport

open Finset PaperP1.Affine PaperP1.PhysicalLabelSupportCount

variable {V A : Type*} [Fintype V] [DecidableEq V] [AddCommGroup A] [Module 𝔽₂ A] [DecidableEq A]

omit [Fintype V] [DecidableEq V] in
theorem odd_class_sum (ℓ : V → A) (R : Finset V) (α : A)
    (hodd : (∑ _v ∈ R.filter (fun v ↦ ℓ v = α), (1 : 𝔽₂)) = 1) :
    (∑ v ∈ R.filter (fun v ↦ ℓ v = α), ℓ v) = α := by
  calc
    _ = ∑ _v ∈ R.filter (fun v ↦ ℓ v = α), (1 : 𝔽₂) • α := by
      apply sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2, one_smul]
    _ = (∑ _v ∈ R.filter (fun v ↦ ℓ v = α), (1 : 𝔽₂)) • α := sum_smul.symm
    _ = _ := by rw [hodd, one_smul]

theorem bounded_support (ℓ : V → A) (S : Finset A) (d : ℕ) (R : Finset V) (α : A)
    (hα : α ≠ 0) (hR : R.card ≤ d + 1) (hzero : (∑ v ∈ R, ℓ v) = 0)
    (hlabels : ∀ v ∈ R, ℓ v ≠ 0 → ℓ v ∈ S)
    (hodd : (∑ _v ∈ R.filter (fun v ↦ ℓ v = α), (1 : 𝔽₂)) = 1) :
    ∃ v ∈ R, ℓ v = α ∧ ∃ D : Finset V,
      D ⊆ R.filter (fun w ↦ ℓ w ≠ α) ∧ D ∈ supportPool ℓ S d α ∧
      2 ≤ D.card ∧ D.card ≤ d ∧ Set.InjOn ℓ (D : Set V) ∧
      (∑ w ∈ D, ℓ w) = α ∧ v ∉ D ∧ 3 ≤ (insert v D).card ∧
      insert v D ⊆ R ∧ (∑ w ∈ insert v D, ℓ w) = 0 := by
  have hsum := odd_class_sum ℓ R α hodd
  have hne : (R.filter fun v ↦ ℓ v = α).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn, sum_empty] at hsum
    exact hα hsum.symm
  obtain ⟨v, hv⟩ := hne
  have hsplit := sum_filter_add_sum_filter_not R (fun v ↦ ℓ v = α) ℓ
  have hrest : (∑ w ∈ R.filter (fun w ↦ ℓ w ≠ α), ℓ w) = α := by
    apply (PaperP1.PairFourierIntersection.add_zero_iff _ _).mp
    have h := hsplit
    rw [hsum, hzero] at h
    simpa only [add_comm] using h
  have hcount := card_filter_add_card_filter_not (s := R) (p := fun v ↦ ℓ v = α)
  have hpositive : 0 < (R.filter fun w ↦ ℓ w = α).card := card_pos.mpr ⟨v, hv⟩
  have hsize : (R.filter fun w ↦ ℓ w ≠ α).card ≤ d := by
    have hcount' : (R.filter fun w ↦ ℓ w = α).card + (R.filter fun w ↦ ℓ w ≠ α).card = R.card := by
      simpa only [ne_eq] using hcount
    omega
  obtain ⟨D, hD, hpool, hDne, hDsize, hDinj, hDsum⟩ :=
    RegularizedSupportPools.support_pool_contains ℓ S d (R.filter fun w ↦ ℓ w ≠ α)
      (fun w hw ↦ hlabels w (mem_filter.mp hw).1) hsize α hα hrest
  have htwo : 2 ≤ D.card := by
    by_contra hn
    have hone : D.card = 1 := by have hp := hDne.card_pos; omega
    obtain ⟨w, hwD⟩ := card_eq_one.mp hone
    have hw : w ∈ D := hwD.symm ▸ mem_singleton_self w
    have hwa : ℓ w = α := by simpa only [hwD, sum_singleton] using hDsum
    exact (mem_filter.mp (hD hw)).2 hwa
  have hvR := (mem_filter.mp hv).1
  have hva := (mem_filter.mp hv).2
  have hvnot : v ∉ D := fun hvD ↦ (mem_filter.mp (hD hvD)).2 hva
  refine ⟨v, hvR, hva, D, hD, hpool, htwo, hDsize, hDinj, hDsum, hvnot, ?_, ?_, ?_⟩
  · rw [card_insert_of_notMem hvnot]
    omega
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact hvR
    · exact (mem_filter.mp (hD hw)).1
  · rw [sum_insert hvnot, hva, hDsum]
    exact PaperP1.PairFourierIntersection.self_add α

theorem source_support {s : ℕ} (ℓ : V → A) (S : Finset A) (d : ℕ) (R : Finset V) (α : A)
    (color : V → Fin s ⊕ Fin 2) (hcolor : Set.InjOn color (R : Set V))
    (hα : α ≠ 0) (hR : R.card ≤ d + 1) (hzero : (∑ v ∈ R, ℓ v) = 0)
    (hlabels : ∀ v ∈ R, ℓ v ≠ 0 → ℓ v ∈ S)
    (hodd : (∑ _v ∈ R.filter (fun v ↦ ℓ v = α), (1 : 𝔽₂)) = 1) :
    ∃ v ∈ R, ℓ v = α ∧ ∃ D : Finset V,
      D ⊆ R.filter (fun w ↦ ℓ w ≠ α) ∧ D ∈ supportPool ℓ S d α ∧
      (∑ w ∈ insert v D, ℓ w) = 0 ∧ insert v D ⊆ R ∧
      ∃ w ∈ insert v D, ∃ i : Fin s, color w = Sum.inl i := by
  obtain ⟨v, hv, hva, D, hD, hpool, _htwo, _hsize, _hinj, _hsum, _hvnot, hthree, hsub, hzeroF⟩ :=
    bounded_support ℓ S d R α hα hR hzero hlabels hodd
  have hsource := TwoFreeBlockSupport.source_mem color (insert v D) (hcolor.mono hsub) hthree
  exact ⟨v, hv, hva, D, hD, hpool, hzeroF, hsub, hsource⟩

end PaperP1.OddLabelCircuitSupport
