module

public import PaperP1.Algebra.HomogeneousLastChartIrreducible

/-! # The literal last chart of a monic P3 equation has its full primitive degree, irreducibility and exact evaluation

Coefficient-field transport and last-variable specialization commute with
the first-variable polynomial presentation. All affine coefficient degree
bounds and evaluations use the same literal polynomial.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.MonicP3LastChart
open Polynomial
open MvPolynomial

section Transport
variable {R S : Type*} [CommRing R] [CommRing S]

theorem finSucc_C (n : ℕ) (r : R) :
    finSuccEquiv R n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) :=
  (finSuccEquiv R n).commutes r

theorem dehom_C (n : ℕ) (r : R) : PaperP1.LastChartPolynomial.dehomogenize (n := n)
    (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [PaperP1.LastChartPolynomial.dehomogenize]

theorem dehom_X_cast (n : ℕ) (i : Fin n) : PaperP1.LastChartPolynomial.dehomogenize
    (MvPolynomial.X i.castSucc : MvPolynomial (Fin (n+1)) R) = MvPolynomial.X i := by
  simp [PaperP1.LastChartPolynomial.dehomogenize]

theorem dehom_X_last (n : ℕ) : PaperP1.LastChartPolynomial.dehomogenize
    (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n+1)) R) = 1 := by
  simp [PaperP1.LastChartPolynomial.dehomogenize]

theorem finSucc_map (φ : R →+* S) (n : ℕ) (P : MvPolynomial (Fin (n+1)) R) :
    finSuccEquiv S n (MvPolynomial.map φ P) =
      Polynomial.map (MvPolynomial.map φ) (finSuccEquiv R n P) := by
  have he : (finSuccEquiv S n).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom (MvPolynomial.map φ)).comp (finSuccEquiv R n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change finSuccEquiv S n (MvPolynomial.map φ (C r)) =
        Polynomial.map (MvPolynomial.map φ) (finSuccEquiv R n (C r))
      rw [MvPolynomial.map_C]
      have hR : finSuccEquiv R n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := (finSuccEquiv R n).commutes r
      have hS : finSuccEquiv S n (MvPolynomial.C (φ r)) = Polynomial.C (MvPolynomial.C (φ r)) := (finSuccEquiv S n).commutes (φ r)
      rw [hR, hS, Polynomial.map_C, MvPolynomial.map_C]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change finSuccEquiv S n (MvPolynomial.map φ (X 0)) =
          Polynomial.map (MvPolynomial.map φ) (finSuccEquiv R n (X 0))
        rw [MvPolynomial.map_X, finSuccEquiv_X_zero, finSuccEquiv_X_zero, Polynomial.map_X]
      · change finSuccEquiv S n (MvPolynomial.map φ (X j.succ)) =
          Polynomial.map (MvPolynomial.map φ) (finSuccEquiv R n (X j.succ))
        rw [MvPolynomial.map_X, finSuccEquiv_X_succ, finSuccEquiv_X_succ, Polynomial.map_C, MvPolynomial.map_X]
  exact RingHom.congr_fun he P
end Transport

variable {F : Type*} [Field F]

def chart : MvPolynomial (Fin 4) F →+* (MvPolynomial (Fin 2) F)[X] :=
  (finSuccEquiv F 2).toRingHom.comp PaperP1.LastChartPolynomial.dehomogenize

theorem factor (P : MvPolynomial (Fin 4) F) : chart P =
    (finSuccEquiv F 3 P).map (PaperP1.LastChartPolynomial.dehomogenize (R := F) (n := 2)) := by
  have he : chart (F := F) =
      (Polynomial.mapRingHom (PaperP1.LastChartPolynomial.dehomogenize (R := F) (n := 2))).comp
        (finSuccEquiv F 3).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.C r)) =
        Polynomial.map _ (finSuccEquiv F 3 (MvPolynomial.C r))
      rw [dehom_C, finSucc_C, finSucc_C, Polynomial.map_C, dehom_C]
    · intro i
      fin_cases i
      · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (0 : Fin 3).castSucc)) =
          Polynomial.map _ (finSuccEquiv F 3 (MvPolynomial.X 0))
        rw [dehom_X_cast, finSuccEquiv_X_zero, finSuccEquiv_X_zero, Polynomial.map_X]
      · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (1 : Fin 3).castSucc)) =
          Polynomial.map _ (finSuccEquiv F 3 (MvPolynomial.X (0 : Fin 3).succ))
        rw [dehom_X_cast, finSuccEquiv_X_succ, Polynomial.map_C]
        change finSuccEquiv F 2 (MvPolynomial.X (0 : Fin 2).succ) =
          Polynomial.C (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (0 : Fin 2).castSucc))
        rw [finSuccEquiv_X_succ, dehom_X_cast]
      · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (2 : Fin 3).castSucc)) =
          Polynomial.map _ (finSuccEquiv F 3 (MvPolynomial.X (1 : Fin 3).succ))
        rw [dehom_X_cast, finSuccEquiv_X_succ, Polynomial.map_C]
        change finSuccEquiv F 2 (MvPolynomial.X (1 : Fin 2).succ) =
          Polynomial.C (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (1 : Fin 2).castSucc))
        rw [finSuccEquiv_X_succ, dehom_X_cast]
      · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (Fin.last 3))) =
          Polynomial.map _ (finSuccEquiv F 3 (MvPolynomial.X (2 : Fin 3).succ))
        rw [dehom_X_last, map_one, finSuccEquiv_X_succ, Polynomial.map_C]
        change 1 = Polynomial.C (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (Fin.last 2)))
        rw [dehom_X_last, Polynomial.C_1]
  exact RingHom.congr_fun he P

theorem monic (q : MvPolynomial (Fin 4) F) (hm : (finSuccEquiv F 3 q).Monic) : (chart q).Monic := by
  rw [factor]
  exact hm.map _

theorem natDegree (q : MvPolynomial (Fin 4) F) {d : ℕ} (hq : q.IsHomogeneous d)
    (hm : (finSuccEquiv F 3 q).Monic) : (chart q).natDegree = d := by
  rw [factor, hm.natDegree_map]
  exact PaperP1.HomogeneousLastChartIrreducible.outer_degree 3 q hq hm

theorem irreducible (q : MvPolynomial (Fin 4) F) (hi : Irreducible q)
    {d : ℕ} (hd : 0 < d) (hq : q.IsHomogeneous d) (hm : (finSuccEquiv F 3 q).Monic) :
    Irreducible (chart q) := by
  exact (MulEquiv.irreducible_iff (finSuccEquiv F 2)).mpr
    (PaperP1.HomogeneousLastChartIrreducible.monic_irreducible 2 q hi hd hq hm)

theorem coefficient_degree (q : MvPolynomial (Fin 4) F) {d : ℕ} (hq : q.IsHomogeneous d) (i : ℕ) :
    ((chart q).coeff i).totalDegree ≤ d := by
  by_cases hc : (chart q).coeff i = 0
  · simp only [hc, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le d
  · have hh := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le
      (PaperP1.LastChartPolynomial.dehomogenize q) i hc
    exact (Nat.le_add_right _ _).trans
      (hh.trans (PaperP1.HomogeneousLastChartNonzero.chart_degree_le q hq))

theorem chart_C (r : F) : chart (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [factor, finSucc_C, Polynomial.map_C, dehom_C]

theorem chart_variables (i : Fin 4) : chart (MvPolynomial.X i : MvPolynomial (Fin 4) F) =
    ![Polynomial.X, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1), 1] i := by
  fin_cases i
  · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (0 : Fin 3).castSucc)) = _
    rw [dehom_X_cast, finSuccEquiv_X_zero]
    rfl
  · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (1 : Fin 3).castSucc)) = _
    rw [dehom_X_cast]
    change finSuccEquiv F 2 (MvPolynomial.X (0 : Fin 2).succ) = _
    exact finSuccEquiv_X_succ
  · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (2 : Fin 3).castSucc)) = _
    rw [dehom_X_cast]
    change finSuccEquiv F 2 (MvPolynomial.X (1 : Fin 2).succ) = _
    exact finSuccEquiv_X_succ
  · change finSuccEquiv F 2 (PaperP1.LastChartPolynomial.dehomogenize (MvPolynomial.X (Fin.last 3))) = _
    rw [dehom_X_last, map_one]
    rfl

theorem evaluation {A : Type*} [CommRing A] [Algebra F A]
    (q : MvPolynomial (Fin 4) F) (v : Fin 2 → A) (y : A) :
    (chart q).eval₂ (MvPolynomial.aeval v).toRingHom y =
      MvPolynomial.aeval (Fin.snoc (Fin.cons y v) 1) q := by
  let φ : (MvPolynomial (Fin 2) F)[X] →+* A := Polynomial.eval₂RingHom (MvPolynomial.aeval v).toRingHom y
  have he : φ.comp (chart (F := F)) = (MvPolynomial.aeval (Fin.snoc (Fin.cons y v) 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change φ (chart (MvPolynomial.C r)) = MvPolynomial.aeval (Fin.snoc (Fin.cons y v) 1) (MvPolynomial.C r)
      rw [chart_C, MvPolynomial.aeval_C]
      change (Polynomial.C (MvPolynomial.C r)).eval₂ (MvPolynomial.aeval v).toRingHom y = _
      rw [Polynomial.eval₂_C]
      exact MvPolynomial.aeval_C v r
    · intro i
      change φ (chart (MvPolynomial.X i)) = MvPolynomial.aeval (Fin.snoc (Fin.cons y v) 1) (MvPolynomial.X i)
      rw [chart_variables, MvPolynomial.aeval_X]
      fin_cases i
      · change (Polynomial.X : (MvPolynomial (Fin 2) F)[X]).eval₂ (MvPolynomial.aeval v).toRingHom y = y
        exact Polynomial.eval₂_X _ _
      · change (Polynomial.C (MvPolynomial.X 0)).eval₂ (MvPolynomial.aeval v).toRingHom y = v 0
        rw [Polynomial.eval₂_C]
        exact MvPolynomial.aeval_X v 0
      · change (Polynomial.C (MvPolynomial.X 1)).eval₂ (MvPolynomial.aeval v).toRingHom y = v 1
        rw [Polynomial.eval₂_C]
        exact MvPolynomial.aeval_X v 1
      · change φ 1 = 1
        exact map_one φ
  exact RingHom.congr_fun he q

end PaperP1.MonicP3LastChart
