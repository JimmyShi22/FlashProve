-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndHeadForms.lean: what objectsF adds, as a list of forms
(`objectsF_forms_from`, OnBytes/Tie/Pv/Tail/EndFormsFrom.lean), at one run of the check of the
head's sub-proof, with that theorem's premises on the state and on the record paid from the run.

Theorems with their proofs. The run is given taken apart, as the record `HeadRan` of
OnBytes/Tie/Pv/Tail/EndHeadRan.lean has it. It does at the head what
OnBytes/Tie/Pv/Tail/EndInvRuns.lean and EndFormsRuns.lean do at attention and the layers.

Main names:
  `head_hear_sized`: behind `Head.hear` the state has one coefficient for each slot.
  `headRan_state`: of the state F22 that objectsF takes: one coefficient for each slot; the plan's
    number of claims is hp.nLin; the batching element is that of the state F8 behind the draw.
  `ownerHeld_fits`, `planH2_fits`, `headRan_fits`: the shapes fit the matrices: at the plan's
    record, and at the record tlA with which objectsF is called.
  `headRan_forms`: the conclusion of `objectsF_forms_from`, with the plan's own number of claims.

Limits: for `headRan_forms` the run must begin at the plan's state. `ReadsRaw` at the cells of m
(OnBytes/Tie/Pv/Tail/EndRaw.lean) is a premise. The lay Y is a free letter. Of what the lookup's
claims add to the total nothing is said. The plan is taken as the value that the planning routine
returns. The plan with which the verifier runs differs from it: at attention the routine
attentionOwners fills one record of the list plFor in the plan's record (the number of the sub-proof
that owns the matrix, and the array's place: borderMeans); at the head the weights are taken off all
virtual rows of the state.


-/
import OnBytes.Tie.Pv.Tail.EndFormsRuns
import OnBytes.Tie.Pv.Tail.EndHeadRows
import OnBytes.Tie.Pv.Tail.EndStepsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.StepsW OnBytes.Road.Rows

/-- Behind `Head.hear` the state has one coefficient for each slot: its second step sets up the
slots, and the steps behind it keep that. -/
theorem head_hear_sized (hS : Head.Shape) (Lh : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (x : Head.Heard) (F G : Fork) (c c' : Ctx)
    (hr : Head.hear hS Lh hp cov plain F c = .ok ((x, G), c')) : G.LS.size = G.ns := by
  unfold Head.hear at hr
  obtain ⟨_, Fa, ca, -, h1⟩ := (Port.bind_ok _ _ _ _ _).1 hr
  obtain ⟨_, Fb, cb, h2, h3⟩ := (Port.bind_ok _ _ _ _ _).1 h1
  obtain ⟨H, hH, e⟩ := (OnBytes.PscRun.change_ok _ Fa ca _).1 h2
  have e2 : Fb = H := congrArg (fun z : (Unit × Fork) × Ctx => z.1.2) e
  have s : Fb.LS.size = Fb.ns := by
    rw [e2, ← Option.some.inj hH]
    exact slots_sized _ _
  exact (Stp.out (R := Inv) (self := by stp) _ _ _ _ _ h3 s).1

/-- The comparison with the plan of the last group of layers keeps that the shapes fit. -/
theorem ownerHeld_fits (O : Head.Owner) (NGr : Nat) (tl tl' : HTailF2) (Fp : Fork) (Tp : Tail2)
    (h : Head.ownerHeld O NGr tl Fp Tp = .ok tl') (hf : Port.Fits tl) : Port.Fits tl' := by
  unfold Head.ownerHeld at h
  dsimp only at h
  split at h
  · obtain ⟨y, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlB, hbm, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact borderMeans_fits hbm hf
  · exact absurd h (throw_bind_ne _ _ _)

/-- The plan's record of the head's sub-proof has shapes that fit its matrices. -/
theorem planH2_fits (g : Settings) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (h : Head.planH2 g hS Lh b O NGr lkW = .ok hp) : Port.Fits hp.tl := by
  unfold Head.planH2 at h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tl0, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨⟨tla, Fa, Ta⟩, hadd, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨Tp, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨tlF, ho, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨_, -, h⟩ := (excBind_ok _ _ _).1 h
    obtain rfl := Except.ok.inj h
    exact ownerHeld_fits _ _ _ _ _ _ ho (addTreesF_fits _ _ _ _ _ _ _ _ _ _ hadd).1
  · exact absurd h (throw_bind_ne _ _ _)

section
variable {hS : Head.Shape} {Lh : Head.HL} {b : Head.Border} {hp : Head.HPlanH2} {O : Head.Owner}
  {cov : Head.Covered} {wsLay : WsLay} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx} {wo : WsForkOut}
  {iU3 : Nat} {x : Head.Heard} {t : Head.Tables} {Rn : Head.Run} {claim : WsClaim}
  {tl1 tlA tl : HTailF2} {laid : Nat} {L2 L4 L8 : LinkCtx}
 {F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25
  F26 F27 F28 F29 F30 F31 : Fork}
 {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26
  c27 c28 c29 c30 c31 : Ctx}

/-- The state that objectsF takes. -/
theorem headRan_state {F : Fork}
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) :
    F22.LS.size = F22.ns ∧ F22.planClaimsF = hp.nLin ∧ F22.theta = F8.theta := by
  have s1 := head_hear_sized hS Lh hp cov _ x F0 F1 c c1 X.hear
  have s2 := (runSL (R := Inv) (x := rootInH [iU3]) inferInstance X.root s1).1
  have s3 := (runS (R := Inv) inferInstance X.tables s2).1
  have s4 := (runSL (R := Inv) (x := tl1.transcriptF) inferInstance X.transcript s3).1
  have s5 := (runS (R := Inv) inferInstance X.weights s4).1
  have s6 := (runS (R := Inv) inferInstance X.merge s5).1
  obtain ⟨k, e, -⟩ := first_state hp.nLin _ _ _ F6 F7 F8 _ _ _ _ _ X.setPlan X.batch
  have k9 : Inv F8 F9 := runS inferInstance X.objects
  have k10 : Inv F9 F10 := runS inferInstance X.note1
  have k11 : Inv F10 F11 := runS inferInstance X.squares
  have k12 : Inv F11 F12 := runS inferInstance X.note2
  have k13 : Inv F12 F13 := runS inferInstance X.ledger
  have k14 : Inv F13 F14 := runS inferInstance X.note3
  have k15 : Inv F14 F15 := runS inferInstance X.stream
  have k16 : Inv F15 F16 := runS inferInstance X.note4
  have k17 : Inv F16 F17 := runS inferInstance X.join
  have k18 : Inv F17 F18 := runS inferInstance X.note5
  have k19 : Inv F18 F19 := runS inferInstance X.policy
  have k20 : Inv F19 F20 := runS inferInstance X.note6
  have k21 : Inv F20 F21 := runS inferInstance X.planes
  have k22 : Inv F21 F22 := runS inferInstance X.note7
  obtain ⟨a, b', d⟩ :=
    (((((((((((((k9.trans k10).trans k11).trans k12).trans k13).trans k14).trans k15).trans
    k16).trans k17).trans k18).trans k19).trans k20).trans k21).trans k22)
      (k s6)
  exact ⟨a, b'.trans e, d⟩

/-- The record with which objectsF is called has shapes that fit its matrices. -/
theorem headRan_fits {F : Fork} (g : Settings) (NGr lkW : Nat)
    (hplan : Head.planH2 g hS Lh b O NGr lkW = .ok hp)
   (X : HeadRan hS Lh b hp O cov wsLay L F c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2 L4 L8
      F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24
      F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
      c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31) : Port.Fits tlA := by
  have f0 := planH2_fits g hS Lh b O NGr lkW hp hplan
  have e2 := closeFuns_spec hp.tl tl1 _ X.closed
  have f2 : Port.Fits tl1 := f0.of_same (by rw [e2]) (by rw [e2]) (by rw [e2])
  exact fits_transcriptF tl1 tlA _ _ _ _ _ _ X.transcript f2

variable {K : Type} [Field K] {J : Type} [Fintype J] (Y : Lay J) (ρ : Reading K) (W : World K)

/-- What objectsF adds at the head, as a list of forms. -/
theorem headRan_forms (g : Settings) (NGr lkW : Nat)
    (hplan : Head.planH2 g hS Lh b O NGr lkW = .ok hp)
   (X : HeadRan hS Lh b hp O cov wsLay L hp.Fp c wo L' F' c' iU3 x t Rn claim tl1 tlA tl laid L2
      L4 L8 F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23
      F24 F25 F26 F27 F28 F29 F30 F31 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17
      c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31)
    (m : J → K) (hW : ReadsRaw ρ tl Rn.t.funs F30 W fun t r c => Y.cellAt m t r c) :
    ((rowsForm Y ρ tlA Rn.t.funs hp.nLin).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tlA Rn.t.funs hp.nLin,
      hp.nLin ≤ p.1 ∧ p.1 ≤ hp.nLin + topOf tlA Rn.t.funs - 1) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tlA.heard = some g ∧ Forest.objects g F22 c22 = .ok (((), Fa), ca) ∧
      tlA.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      c23 = cc ∧ Kept Fc F23 ∧
      F23.nClaim = Fc.nClaim + tlA.NM + (readsList tlA Rn.t.funs).length ∧
      F23.total ρ W = Fc.total ρ W +
        (batchAt (ρ.val F22.theta) (rowsForm Y ρ tlA Rn.t.funs hp.nLin)).gap m := by
  have hV := headRan_rawRows ρ g NGr lkW hplan X W _ hW
  rw [(objectsF_keeps tlA tl Rn.t.funs F22 F23 c22 c23 X.objectsF (headRan_state X).1).2.2] at hV
  have h := objectsF_forms_from Y ρ W tlA tl Rn.t.funs F22 F23 c22 c23 X.objectsF
    (headRan_fits g NGr lkW hplan X) (headRan_state X).1 m hV
  rw [(headRan_state X).2.1] at h
  exact h

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.headRan_state
#print axioms OnBytes.Tie.Pv.Tail.headRan_fits
#print axioms OnBytes.Tie.Pv.Tail.headRan_forms
