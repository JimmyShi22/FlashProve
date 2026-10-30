-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Weights2.lean: the law of kind K5 at the library's letters: the weights of
two
sumchecks that read the lookup's point: the denominator times the output (wDivision) and the value
product on
the diagonal (wOn): read as the library's weight polynomials Wb … .s8 and .s12 at the output's
point.

Main names:
  `LookPts ρ D C z pw zW`: the lookup's points' premises: the pieces' weights read as the library's
    wp … .w3;
    the cuts of the inner point read as yg, yi, yI.
  `asPW`, `timesW_asPW`: the kind's "pw.map (mulE · f)" is the library's timesW at the pieces made
    of pw.
  `division_weight`, `on_weight`, `division_hW`, `on_hW`.

Limit: LookPts ties the key points that the lookup's kind hands on to the typed first statement's
lookup
point; it is not shown in this file or in what it imports.
Sources: Johnson/Road/Rows/AttRows14.lean (weightProduct); AttRows58.lean (weightOn); AttWb14.lean
(wbExt8);
Cb/Pv/Att/Mean/Weights.lean (wbExt12); OnBytes/Model/AttentionHeard.lean (PW, timesW);
Inst/Model/Att.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttRows14
import Johnson.Road.Rows.AttWb14
import Johnson.Desc.First.Att.K05Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH)
open OnBytes.Attention (PW timesW)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- The pieces made of bare weights. -/
def asPW (pw : Array E) : Array PW := pw.map fun w => { lam := 0, a := 0, wp := w }

theorem timesW_asPW (pw : Array E) (f : E) : timesW (asPW pw) f = pw.map (mulE · f) := by
  unfold timesW asPW
  rw [Array.map_map]
  rfl

theorem asPW_wp (pw : Array E) (b : ℕ) (hb : b < pw.size) : ((asPW pw).getD b default).wp = pw.getD b zeroE := by
  unfold asPW
  simp [Array.getD_eq_getD_getElem?, hb]

/-- **The lookup's points' premises.** -/
structure LookPts (ρ : Reading K) (D : AttSeg.Dim) (C : AttSeg.Calls) (z : ℕ → K) (pw zW : Array E) : Prop where
  nPw : pw.size = D.nb
  nZ : 1 + D.lg + D.lT ≤ zW.size
  hw : ∀ b < D.nb, ρ.val (pw.getD b zeroE) = AttSeg.wp D C z .w3 b
  hg : ∀ k < D.lg, ρ.val (zW.getD (1 + k) zeroE) = AttSeg.yg D C z k
  hi : ∀ k < D.lT, ρ.val (zW.getD (1 + D.lg + k) zeroE) = AttSeg.yi D C z k
  hI : ∀ k < D.lP + 1, ρ.val (zW.getD (1 + D.lg + k) zeroE) = AttSeg.yI D C z k

omit [Fintype K] in
/-- K5's weights of the denominator times the output read as the library's weight. -/
theorem division_weight (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub K) (g : Geo) (h : Heard) {pw zW : Array E}
    (lp : LookPts ρ D C p.z pw zW) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg)
    (hr : D.lg + D.lT ≤ (chal h.division).size) {b : ℕ} (hb : b < D.nb) :
    ρ.val ((wDivision g pw zW h).getD b zeroE) =
      AttSeg.Wb D C p .s8 b fun j => ρ.val ((chal h.division).getD j zeroE) := by
  unfold wDivision
  rw [g1, g2]
  have hbs : b < (asPW pw).size := by
    unfold asPW
    rw [Array.size_map, lp.nPw]
    exact hb
  have hn := lp.nZ
  have := OnBytes.Road.Rows.weightProduct ρ D C p (pwW := asPW pw) (zgW := zW.extract 1 (1 + D.lg))
    (ziW := zW.extract (1 + D.lg) (1 + D.lg + D.lT)) (r := chal h.division) hbs (by simp; omega) (by simp; omega) hr
    (by rw [asPW_wp pw b (by rw [lp.nPw]; exact hb)]; exact lp.hw b hb)
    (fun k hk => by
      show ρ.val ((zW.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact lp.hg k hk)
    (fun k hk => by
      show ρ.val ((zW.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact lp.hi k hk)
  rw [timesW_asPW] at this
  exact this

omit [Fintype K] in
/-- K5's weights of the value product on the diagonal read as the library's weight. -/
theorem on_weight (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub K) (g : Geo) (h : Heard) {pw zW : Array E}
    (lp : LookPts ρ D C p.z pw zW) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg) (g3 : g.lnT = D.lP + 1)
    (hr : D.lg + (D.lP + 1) ≤ (chal h.on).size) {b : ℕ} (hb : b < D.nb) :
    ρ.val ((wOn g pw zW h).getD b zeroE) = AttSeg.Wb D C p .s12 b fun j => ρ.val ((chal h.on).getD j zeroE) := by
  unfold wOn
  rw [g1, g2, g3]
  have hbs : b < (asPW pw).size := by
    unfold asPW
    rw [Array.size_map, lp.nPw]
    exact hb
  have hn := lp.nZ
  have hT : D.lT = D.lP + 1 + D.lB := rfl
  have := OnBytes.Road.Rows.weightOn ρ D C p (pwW := asPW pw) (zgW := zW.extract 1 (1 + D.lg))
    (zihi := (zW.extract (1 + D.lg) (1 + D.lg + D.lT)).extract 0 (D.lP + 1)) (r := chal h.on) hbs (by simp; omega)
    (by simp; omega) hr
    (by rw [asPW_wp pw b (by rw [lp.nPw]; exact hb)]; exact lp.hw b hb)
    (fun k hk => by
      show ρ.val ((zW.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact lp.hg k hk)
    (fun k hk => by
      show ρ.val (((zW.extract _ _).extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega), extract_getD _ _ _ _ (by omega), Nat.zero_add]
      exact lp.hI k hk)
  rw [timesW_asPW] at this
  exact this

/-- **The denominator times the output: the typed weight at the output's point is the reading of
K5's weight.** -/
theorem division_hW {X J : Type} [Fintype J] (D : AttSeg.Dim) (Cc : AttSeg.Calls)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (AttSeg.Step.s8.g D) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (stepSc3 D Cc rdc .s8 inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {Gf : Fork} (g : Geo) (h : Heard) {pw zW : Array E}
    (hs : SizeP (SumL.of3 (stepSc3 D Cc rdc .s8 inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H h.division)
    (hsum : SumAt C st riders H h.division Gf) (lp : LookPts ρ D Cc Dd.st.z pw zW) (g1 : g.lt = D.lT)
    (g2 : g.lgk = D.lg) (b : Fin D.nb) :
    (stepSc3 D Cc rdc .s8 inc wAt cAt).W Dd.st b
      (ldPartIni (AttSeg.Step.s8.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt) =
        ρ.val ((wDivision g pw zW h).getD b.1 zeroE) := by
  have hsz : (chal h.division).size = AttSeg.Step.s8.g D := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  show Blocks.ext (AttSeg.Step.s8.g D)
    (fun Y => AttSeg.Wb D Cc Dd.st .s8 b.1 (Blocks.cubePt (AttSeg.Step.s8.g D) Y))
    (Blocks.nat (ldPartIni (AttSeg.Step.s8.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [OnBytes.Road.Rows.wbExt8, division_weight D Cc Dd.st g h lp g1 g2 (by rw [hsz]; exact le_refl _) b.2]
  exact congrArg _ hn

/-- **The value product on the diagonal: the typed weight at the output's point is the reading of
K5's weight.** -/
theorem on_hW {X J : Type} [Fintype J] (D : AttSeg.Dim) (Cc : AttSeg.Calls)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (AttSeg.Step.s12.g D) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (stepSc3 D Cc rdc .s12 inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {Gf : Fork} (g : Geo) (h : Heard) {pw zW : Array E}
    (hs : SizeP (SumL.of3 (stepSc3 D Cc rdc .s12 inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H h.on)
    (hsum : SumAt C st riders H h.on Gf) (lp : LookPts ρ D Cc Dd.st.z pw zW) (g1 : g.lt = D.lT)
    (g2 : g.lgk = D.lg) (g3 : g.lnT = D.lP + 1) (b : Fin D.nb) :
    (stepSc3 D Cc rdc .s12 inc wAt cAt).W Dd.st b
      (ldPartIni (AttSeg.Step.s12.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt) =
        ρ.val ((wOn g pw zW h).getD b.1 zeroE) := by
  have hsz : (chal h.on).size = AttSeg.Step.s12.g D := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  show Blocks.ext (AttSeg.Step.s12.g D)
    (fun Y => AttSeg.Wb D Cc Dd.st .s12 b.1 (Blocks.cubePt (AttSeg.Step.s12.g D) Y))
    (Blocks.nat (ldPartIni (AttSeg.Step.s12.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [wbExt12, on_weight D Cc Dd.st g h lp g1 g2 g3 (by
    rw [hsz]
    show D.lg + (D.lP + 1) ≤ D.lg + (D.lP + 1) + D.lB
    omega) b.2]
  exact congrArg _ hn

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.division_hW
#print axioms VerifiableInference.Desc.First.Att.P.on_hW
#print axioms VerifiableInference.Desc.First.Att.P.division_weight
