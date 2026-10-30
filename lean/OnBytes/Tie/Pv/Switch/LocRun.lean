-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Switch/LocRun.lean: a run of the program's code switch in the form that leaves its
claims as open rows (`csSigmaVerify`, OnBytes/Iop/Cs.lean), cut at its calls.

OnBytes/Slice/BlkCsRun.lean cuts the other form of the switch, which draws an element after the
positions (`switchVerify_inv`: the round is named CS), for a target without kept members. A
request's chain uses the form without that element between two of its groups (the round is named
LOC), with kept members and with further sampled oracle messages in the same prover's message. This
file has the cut for that form, for every target. No arithmetic. Statements and proofs.

Main names:
  `sentAll T others`: the oracle messages of the switch's prover's message, in order: the target,
    the oracle messages that take the kept members' rows, the others.
  `switchVerify_loc_inv`: what a run of `switchVerify old T gp others false` has done, call by call:
    the target was checked; SEND ran on `sentAll T others` and left the round of its answers open; a
    round named LOC was closed, whose entry has the old code's range and at least one position, and
    which drew no element; what is returned names the oracle messages by their places in the sending
    and has the positions drawn; the old rows were read at these positions; the claims were
    admitted.
  `csSigmaVerify_inv`: the same of `csSigmaVerify`.
Limits: nothing on what SEND, the reading of the old rows or the admission have done (for one
sampled oracle message and no kept member: OnBytes/Slice/BlkCsRun.lean, `sendOne_inv`,
`singleRowsRead_inv`,
`switchAdmit_inv`). Nothing on a dry run. Nothing on soundness.

-/
import OnBytes.Slice.BlkCsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice

/-- The oracle messages of the prover's message of a switch. -/
def sentAll (T : SwitchTarget) (others : Array OracleNotice) : Array OracleNotice :=
  #[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++
    T.kept.map (fun k => (⟨k.shape, k.leafClass⟩ : OracleNotice)) ++ others

/-- A run of the switch that draws no element after the positions, cut at its calls. ids: the
numbers of the oracle messages sent; cA: the context after the sending; d: what the round of the
positions drew; cB: the context after that round; y: the symbols read; cC: the context after the
reading; cD: the same with intermediate values kept. -/
theorem switchVerify_loc_inv (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (z : E) (c c' : Ctx)
    (h : (switchVerify old T gp others false).Yields c (out, z) c') :
    ∃ ids cA code d e cB y cC cD,
      switchTargetCheck c.st old T = true ∧
      (sendVerify (sentAll T others) false).Yields c ids cA ∧
      c.st.codes.base[old.code]? = some code ∧
      (Blk.close "LOC" .positions).Yields cA d cB ∧ cB.ch.last = some e ∧ e.logN = code.logN ∧
      0 < e.poss ∧ d.elems.map E.ofTriple = [] ∧ z = zeroE ∧
      out = { g := ids.getD 0 noId, kept := ids.extract 1 (1 + T.kept.size),
              others := ids.extract (1 + T.kept.size) ids.size,
              positions := Positions.ofDraws code.logN d.poss } ∧
      (singleRowsRead old out.positions).Yields cB y cC ∧ Blk.SameButNotes cC cD ∧
      (switchAdmit old T gp out y).Yields cD () c' := by
  unfold switchVerify at h
  obtain ⟨S, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, rfl⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hcheck, rfl⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨ids, cA, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨code, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨hcode, e4⟩ := (Blk.yields_get _ _ _ _).1 h4
  subst e4
  obtain ⟨drawn, cB, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨d, e, hclose, hlast, hlog, hpos, rfl⟩ := closePositions_inv _ _ _ _ _ h5
  -- the round has drawn no element after the positions
  change (match false, d.elems.map E.ofTriple with
    | true, [x] => _
    | false, [] => _
    | _, _ => _ : Blk (Switched × E)).Yields cB (out, z) c' at a5
  cases hel : d.elems.map E.ofTriple with
  | cons x l =>
    rw [hel] at a5
    obtain ⟨_, _, k, _⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
    cases k
  | nil =>
    rw [hel] at a5
    obtain ⟨_, c6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
    obtain ⟨rfl, e6⟩ := (Blk.yields_pure _ _ _ _).1 h6
    subst e6
    obtain ⟨y, cC, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
    obtain ⟨_, c8, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
    obtain ⟨_, c9, h9, a9⟩ := (Blk.yields_bind _ _ _ _ _).1 a8
    obtain ⟨_, cD, h10, a10⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
    obtain ⟨_, c11, h11, a11⟩ := (Blk.yields_bind _ _ _ _ _).1 a10
    obtain ⟨hout, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a11
    obtain ⟨eo, ez⟩ := Prod.mk.inj hout
    have n1 := Blk.yields_noteBy _ _ _ _ h8
    have n2 := Blk.yields_noteBy _ _ _ _ h9
    have n3 := Blk.yields_noteBy _ _ _ _ h10
    have hn : Blk.SameButNotes cC cD :=
      ⟨n3.ch.trans (n2.ch.trans n1.ch), n3.st.trans (n2.st.trans n1.st),
        n3.book.trans (n2.book.trans n1.book), n3.failed.trans (n2.failed.trans n1.failed)⟩
    rw [← eo] at h7 h11
    exact ⟨ids, _, code, d, e, _, y, cC, cD, hcheck, h3, hcode, hclose, hlast, hlog, hpos, hel,
      ez, eo, h7, hn, h11⟩

/-- The same of the form that returns what the switch returns alone. -/
theorem csSigmaVerify_inv (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (c c' : Ctx)
    (h : (csSigmaVerify old T gp others).Yields c out c') :
    ∃ ids cA code d e cB y cC cD,
      switchTargetCheck c.st old T = true ∧
      (sendVerify (sentAll T others) false).Yields c ids cA ∧
      c.st.codes.base[old.code]? = some code ∧
      (Blk.close "LOC" .positions).Yields cA d cB ∧ cB.ch.last = some e ∧ e.logN = code.logN ∧
      0 < e.poss ∧ d.elems.map E.ofTriple = [] ∧
      out = { g := ids.getD 0 noId, kept := ids.extract 1 (1 + T.kept.size),
              others := ids.extract (1 + T.kept.size) ids.size,
              positions := Positions.ofDraws code.logN d.poss } ∧
      (singleRowsRead old out.positions).Yields cB y cC ∧ Blk.SameButNotes cC cD ∧
      (switchAdmit old T gp out y).Yields cD () c' := by
  unfold csSigmaVerify at h
  obtain ⟨p, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨rfl, e1⟩ := (Blk.yields_pure _ _ _ _).1 a1
  subst e1
  obtain ⟨ids, cA, code, d, e, cB, y, cC, cD, k1, k2, k3, k4, k5, k6, k7, k8, -, k10, k11, k12,
      k13⟩ :=
    switchVerify_loc_inv old T gp others p.1 p.2 c _ h1
  exact ⟨ids, cA, code, d, e, cB, y, cC, cD, k1, k2, k3, k4, k5, k6, k7, k8, k10, k11, k12, k13⟩

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.switchVerify_loc_inv
#print axioms OnBytes.Tie.Pv.Switch.csSigmaVerify_inv
