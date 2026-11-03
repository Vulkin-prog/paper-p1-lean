module

public import PaperP1.Asymptotics.TwoTargetNonalignedMixedCount
public import PaperP1.Asymptotics.TwoTargetPureCount
public import PaperP1.Arithmetic.TwoTargetLabelDimension

/-! # A positive actual effective relation dimension gives the full nonaligned half-power pair count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetNonalignedDenseCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetLabelSelection PaperP1.DisjointRecoverySubspace

local instance nonalignedDensePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def HasMixed {s : ℕ} (x : Fin s → ℕ) (L t k : ℕ) (p : ℕ × ℕ) : Prop :=
  ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
    NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
    ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i : Fin k, ∀ j : Fin 2,
        (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).Nonempty

def HasPure {s : ℕ} (x : Fin s → ℕ) (L t : ℕ) (p : ℕ × ℕ) : Prop :=
  ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
    NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
    ∀ j : Fin 2, ∃ α : Fin 2 → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i : Fin 2,
        (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).Nonempty ∧
          targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j.rev = ∅

theorem uniform_pairs (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t Ds k : ℕ, 2 ≤ t ∧ 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k (t - 1) Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
          η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨t, ht, hregularize⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace s η hη
  obtain ⟨Ds, k, hDs, hmixed⟩ := TwoTargetNonalignedMixedCount.uniform_hosts s t ht 1 C ε (by norm_num) hε
  obtain ⟨Np, _hNp, hpure⟩ := TwoTargetPureCount.uniform_pairs s t ht 1 C ε (by norm_num) hε
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (4 * ((k + 2 : ℕ) : ℝ) / (3 * η))
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨t, Ds, k, ht, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨Am, hAm, Nm, hm⟩ := hmixed hCover hPila
  refine ⟨Am + 1, by positivity, max 3 (max Nm (max Np Ng)), by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hnon hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hlarge : ((k + 2 : ℕ) : ℝ) ≤ 3 * η * L / 4 := by
    have hbase := (div_lt_iff₀ (by positivity : 0 < 3 * η)).mp hL₀
    have hLL : (L₀ : ℝ) ≤ L := by exact_mod_cast (show L₀ ≤ L by omega)
    have hmono := mul_le_mul_of_nonneg_left hLL hη.le
    nlinarith only [hbase, hmono]
  have hcases : ∀ p ∈ F, HasMixed x L t k p ∨ HasPure x L t p := by
    intro p hp
    obtain ⟨hWY, hWZ, hdimR⟩ := hdense p hp
    obtain ⟨P, hno, hdim, hinj⟩ := hregularize x p.1 p.2 L hL W hW hWY hWZ
    have hdimP : k + 2 ≤ Module.finrank F₂ P := by
      have h : ((k + 2 : ℕ) : ℝ) ≤ Module.finrank F₂ P := by linarith only [hlarge, hdimR, hdim]
      exact_mod_cast h
    have hlabels (j : Fin 2) : k + 2 ≤ (targetLabels (starts x p.1 p.2) P j).card :=
      hdimP.trans (TwoTargetLabelDimension.dimension_le_labels _ P hinj j)
    rcases mixed_or_two_pure _ P k (hlabels 0) (hlabels 1) with hmixed | hpure
    · exact Or.inl ⟨P, hno, hmixed⟩
    · exact Or.inr ⟨P, hno, hpure⟩
  let mixedHosts := F.filter (HasMixed x L t k)
  let pureHosts := F \ mixedHosts
  have hmcount := hm N (by omega) L (L + 1) hband le_rfl (by norm_num) x hx mixedHosts
    (fun p hp ↦ hdyadic p (mem_filter.mp hp).1)
    (fun p hp ↦ hnon p (mem_filter.mp hp).1)
    (fun _ hp ↦ (mem_filter.mp hp).2)
  have hpcount := hpure N (by omega) L (L + 1) hband le_rfl (by norm_num) x hx pureHosts
    (fun p hp ↦ hdyadic p (mem_sdiff.mp hp).1) (by
      intro p hp
      obtain ⟨hpF, hpnot⟩ := mem_sdiff.mp hp
      exact (hcases p hpF).resolve_left (fun h ↦ hpnot (mem_filter.mpr ⟨hpF, h⟩)))
  have hfinite : (F.card : ℝ) = (mixedHosts.card : ℝ) + pureHosts.card := by
    have h := card_sdiff_add_card_eq_card (show mixedHosts ⊆ F from filter_subset _ _)
    change pureHosts.card + mixedHosts.card = F.card at h
    exact_mod_cast (by omega : F.card = mixedHosts.card + pureHosts.card)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsmall : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc
    _ = (mixedHosts.card : ℝ) + pureHosts.card := hfinite
    _ ≤ Am * (N : ℝ) ^ (1 / 2 + ε) + (N : ℝ) ^ ε := add_le_add hmcount hpcount
    _ ≤ Am * (N : ℝ) ^ (1 / 2 + ε) + (N : ℝ) ^ (1 / 2 + ε) := add_le_add (le_refl _) hsmall
    _ = _ := by ring

end PaperP1.TwoTargetNonalignedDenseCount
