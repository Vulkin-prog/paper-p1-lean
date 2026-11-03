module

public import PaperP1.Asymptotics.TwoTargetWeakMixedCount
public import PaperP1.Asymptotics.TwoTargetWeakRegularization
public import PaperP1.Asymptotics.TwoTargetNonalignedDenseCount

/-! # A positive actual effective relation dimension gives the full weak-aligned half-power pair count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetWeakDenseCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetAllowedLabels PaperP1.TwoTargetUnitExclusion PaperP1.DisjointRecoverySubspace
  PaperP1.TwoTargetNonalignedDenseCount

local instance weakDensePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≤ (L + 1) ^ 3 ∧ b ≤ (L + 1) ^ 3 ∧
    EnlargedPairGeometry.Geometric a b p.1 p.2 L ∧ ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
    NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
    ∃ U : Finset (Fin (L + 1) × Fin (L + 1)), (NormalizedUnitCount.units a b p.1 p.2 L \ U).card ≤ 1 ∧
    ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      (∀ i, α i ∉ excludedLabels (label (starts x p.1 p.2) M) U) ∧
      ∀ i : Fin k, ∀ j : Fin 2,
        (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).Nonempty

theorem uniform_pairs (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t Ds k : ℕ, 2 ≤ t ∧ 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k (t - 1) Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
          (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
        (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
          η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨t, ht, hregularize⟩ := TwoTargetWeakRegularization.uniform_selection_data s η hη
  obtain ⟨Nr, _hNr, hr⟩ := hregularize C
  obtain ⟨Ds, k, hDs, hmixed⟩ := TwoTargetWeakMixedCount.uniform_hosts s t ht 1 C ε (by norm_num) hε
  obtain ⟨Np, _hNp, hpure⟩ := TwoTargetPureCount.uniform_pairs s t ht 1 C ε (by norm_num) hε
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (2 * ((k + 4 : ℕ) : ℝ) / η)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨t, Ds, k, ht, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨Am, hAm, Nm, hm⟩ := hmixed hCover hPila
  refine ⟨Am + 1, by positivity, max 3 (max Nm (max Np (max Ng Nr))), by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic haligned hdense
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hlarge : ((k + 4 : ℕ) : ℝ) ≤ η * L / 2 := by
    have hbase := (div_lt_iff₀ hη).mp hL₀
    have hLL : (L₀ : ℝ) ≤ L := by exact_mod_cast (show L₀ ≤ L by omega)
    have hmono := mul_le_mul_of_nonneg_left hLL hη.le
    nlinarith only [hbase, hmono]
  have hcases : ∀ p ∈ F, HasMixed x L t k p ∨ HasPure x L t p := by
    intro p hp
    obtain ⟨hWY, hWZ, hdimR⟩ := hdense p hp
    obtain ⟨a, b, ha, hb, haH, hbH, hgeom, P, hno, _hsize, U, _hUsub, _hUcard, hremaining, _hE, hpop⟩ :=
      hr N (by omega) L hL hband (η / 64) (by positivity) x W hW p.1 p.2
        (hdyadic p hp).1 (hdyadic p hp).2 hWY hWZ (haligned p hp).1 (haligned p hp).2
    have hlabels (j : Fin 2) : k + 2 ≤
        (allowedLabels (starts x p.1 p.2) P (excludedLabels (label (starts x p.1 p.2) P) U) j).card := by
      have hb := (hpop j).1
      have heq : ((k + 4 : ℕ) : ℝ) = ((k + 2 : ℕ) : ℝ) + 2 := by push_cast; ring
      have h : ((k + 2 : ℕ) : ℝ) ≤
          (allowedLabels (starts x p.1 p.2) P (excludedLabels (label (starts x p.1 p.2) P) U) j).card := by
        linarith only [hlarge, hdimR, hb, heq]
      exact_mod_cast h
    rcases TwoTargetAllowedLabels.mixed_or_two_pure _ P _ k (hlabels 0) (hlabels 1) with hmixed | hpure
    · exact Or.inl ⟨a, b, ha, hb, haH, hbH, hgeom, P, hno, U, hremaining, hmixed⟩
    · apply Or.inr
      refine ⟨P, hno, ?_⟩
      intro j
      obtain ⟨α, hinj, hα, _hsafe, hdata⟩ := hpure j
      exact ⟨α, hinj, hα, hdata⟩
  let mixedHosts := F.filter (HasMixed x L t k)
  let pureHosts := F \ mixedHosts
  have hmcount := hm N (by omega) L (L + 1) hband le_rfl (by norm_num) x hx mixedHosts
    (fun p hp ↦ hdyadic p (mem_filter.mp hp).1)
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

end PaperP1.TwoTargetWeakDenseCount
