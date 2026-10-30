-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public clauses of the first chain's last test, from a shape.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/FitsShapeL.lean: FitsAtL (AtFile/ClosingData.lean) at the plain
data that FrontAsksD names, from one public test on the shape of the state on entry: the twin of the
clause plain of frontFiveB (FrontAtShape.lean). FitsAtL reads the verifier's record (the group's
members, their shapes, the book's tree), which FrontAsksD does not fix; the test reads them at the
shape. So where the shape is one closed term, this is one evaluation at it.

  fitsPlain        the clauses of FitsAtL on the plain data as shapes
  fitsShapeB       the test on the shape
  fits_of_plain    the clauses give FitsAtL
  fits_of_shape    the statement

Limits. That the test says yes at a run's shape is a premise here: it reads testSh T, as frontFiveB
does. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingData
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Sh (PlainS plainSh gpOfS gpOfS_eq batThin thinSh thinOf thinOf_eq TestSh testSh
  logAtS widthAtS logAtS_eq widthAtS_eq)

/-- A seat's clauses, on a seat. -/
abbrev seatClauses (a : Fmt.M1.Stage) (P : VerifiableInference.Desc.K1.Par) (Ly : TreeLay) (k : ℕ)
    (s : Seat1) : Prop :=
  s.sh = shapeAt P k ∧ s.tsh = Ly.shapes.getD (Ly.tree.getD k 0) {} ∧
    s.part = Ly.part.getD k 0 ∧ (s.sh.mainDeg = 1 ∨ s.sh.mainDeg = 3) ∧
    (0 < s.sh.mainRows → codeOf (P.codes.base.getD s.sh.code default) = a.C) ∧
    (0 < s.sh.maskRows → codeOf (P.codes.mask.getD s.sh.maskCode default) = a.Z)

/-- **The clauses of FitsAtL, on the plain data as shapes.** -/
abbrev fitsPlain (q : P12) (p : K2.SwitchPlace) (D : PlainS) (s : Seat1) (Ly : TreeLay) : Prop :=
  VerifiableInference.Desc.K1.planOkOwn (parL p) = true ∧ 1 < (parL p).sent.size ∧
    (sentL p).size = 2 ∧ D.ts = [s.t] ∧ seatClauses (stA q) (parL p) Ly 0 s ∧
    seatClauses (stA q) (parL p) Ly 1 D.fresh ∧ Ly.tree.getD 0 0 = 0 ∧ Ly.tree.getD 1 0 = 0 ∧
    0 < Ly.shapes.size ∧ D.fresh.t = s.t ∧ D.fresh.sh.maskRows = 2 ^ (stA q).h ∧
    s.sh.mainDeg = 3 ∧ s.sh.maskRows = 0 ∧ s.sh.mainRows = 2 ^ kk (stA q) ∧
    OnBytes.ceilLog2 (shapeL p).mainRows = kk (stA q) ∧ oM D.L 0 = 0 ∧
    logAtS D.book s.t =
      (((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.getD 0
        default).logN ∧
    widthAtS D.book s.t = (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth

/-- **The test on the shape.** -/
def fitsShapeB (q : P12) (p : K2.SwitchPlace) (N : TestSh) : Bool :=
  match batThin q (thinOf N) with
  | some aB =>
    match aB.pass with
    | .claim L =>
      match gpOfS q aB (stA q) L with
      | some D =>
        match layTrees (parL p).codes (parL p).sent, D.mems with
        | some Ly, [s] => decide (fitsPlain q p D s Ly)
        | _, _ => false
      | none => false
    | _ => false
  | none => false

/-- The clauses give FitsAtL. -/
theorem fits_of_plain {q : P12} {p : K2.SwitchPlace} {Dp : Plain} {s : Seat1} {Ly : TreeLay}
    (hl : layTrees (parL p).codes (parL p).sent = some Ly) (hm : Dp.mems = [s])
    (h : fitsPlain q p (plainSh Dp) s Ly) : FitsAtL q p Dp s s.t Ly := by
  obtain ⟨h1, h2, h3, h4, ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact
    { plan := h1, lay := hl, two := h2, count := h3, mems := hm, ts := h4
      seat := ⟨a1, a2, a3, a4, a5, a6⟩, fresh := ⟨b1, b2, b3, b4, b5, b6⟩
      tree0 := h7, tree1 := h8, some0 := h9, at0 := rfl, at1 := h10, rowsF := h11
      deg := h12, noMask := h13, rows := h14, logRows := h15, first := h16
      depth := (logAtS_eq _ _).symm.trans h17, width := (widthAtS_eq _ _).symm.trans h18 }

variable {W X : Type}

/-- **The public clauses at the plain data that FrontAsksD names, from one test on the shape.** -/
theorem fits_of_shape (J : TestJob W X) (w : W) (fr : Front X) (K : OnBytes.Codes) (Dp : Plain)
    (pl : K2.SwitchPlace) (he : J.p.early = true) (S : FrontAsksD J w fr K Dp)
    (hp : (J.rec₀ w fr).pass = .nothing) (hB : fitsShapeB J.p pl (testSh (J.rec₀ w fr)) = true) :
    ∃ (s : Seat1) (u : ℕ) (Ly : TreeLay), FitsAtL J.p pl Dp s u Ly := by
  unfold fitsShapeB at hB
  rw [thinOf_eq] at hB
  split at hB
  · rename_i aB haB
    split at hB
    · rename_i L hL
      split at hB
      · rename_i D hD
        split at hB
        · rename_i Ly s hLy hs
          have hg : ∃ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G := by
            cases hg : (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? with
            | some G => exact ⟨G, rfl⟩
            | none =>
              exfalso
              unfold batThin at haB
              have e0 : (thinSh (J.rec₀ w fr)).pass = .nothing := by
                show ProofFile.Honest.Sh.thinPass (J.rec₀ w fr).pass = _
                rw [hp]
                rfl
              rw [e0] at haB
              split at haB
              · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 haB
                have hy' : VerifiableInference.Desc.Ground.Sh.beginRunS
                    (VerifiableInference.Desc.Ground.Sh.shD (H2K.Out.dT (J.rec₀ w fr) []))
                    (J.rec₀ w fr).g = some y := hy
                obtain ⟨x, hx⟩ := VerifiableInference.Desc.Ground.Sh.beginRun_returns
                  (H2K.Out.dT (J.rec₀ w fr) []) (J.rec₀ w fr).g y hy'
                unfold VerifiableInference.Desc.Ground.beginRunP at hx
                split at hx
                · have hg' : (H2K.Out.dT (J.rec₀ w fr) []).st.groups[(J.rec₀ w fr).g]? = none := hg
                  rw [hg'] at hx
                  cases hx
                · cases hx
              · cases haB
          obtain ⟨G, hG⟩ := hg
          have eT := ProofFile.Honest.K12.Thin.thin_batT J.p (J.rec₀ w fr) G {} aB hp he hG haB
          have eL : L = layoutOf (J.rec₀ w fr).st G := by
            have k : (thinSh (batT (J.rec₀ w fr) G {})).pass =
                .claim (layoutOf (J.rec₀ w fr).st G) := rfl
            rw [eT, hL] at k
            injection k
          subst eL
          have k := gpOfS_eq J.p (batT (J.rec₀ w fr) G {}) (stA J.p)
            (layoutOf (J.rec₀ w fr).st G)
          rw [eT, hD, (S.plain G hG).1] at k
          obtain rfl : D = plainSh Dp := Option.some.inj k
          have hm : Dp.mems = [s] := hs
          exact ⟨s, s.t, Ly, fits_of_plain hLy hm (of_decide_eq_true hB)⟩
        · cases hB
      · cases hB
    · cases hB
  · cases hB

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.fitsShapeB
#print axioms ProofFile.Honest.K12.Sim2.fits_of_plain
#print axioms ProofFile.Honest.K12.Sim2.fits_of_shape
