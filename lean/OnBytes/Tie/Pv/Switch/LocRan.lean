-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Switch/LocRan.lean: what a run of the program's code switch between two groups of a
request's chain has taken and made, in one statement.

OnBytes/Tie/Pv/Switch/LocRun.lean cuts a run of `csSigmaVerify` (OnBytes/Iop/Cs.lean) at its calls.
The first of these calls is the sending block, which OnBytes/Slice/BlkSendRun.lean takes apart for
any number of oracle messages and answers. This file puts the two together, for a run on a view. No
arithmetic. Statements and proofs.

Main names:
  `LocTaken`: a record of what the run has taken and made: how the oracle messages sent are placed
    in trees; their numbers; the shapes of those that are sampled; what the round of the seed drew,
    and the seeds cut out of it; the old code; what the round of the positions drew, and its entry
    of the plan; the symbols read; and the contexts between the calls.
  `LocRan old T gp others out c c' D`: what holds of such a record:
    - the target was checked;
    - the oracle messages `sentAll T others` were received: their trees are laid as D.lay says, they
      have the next free numbers, and the context behind is written out;
    - a round named "SEND seed" was closed and drew D.dS; the seeds are cut out of it, as many as
      the largest number of answers, over as many coordinates as the largest cube has; no seed's
      factor is 0;
    - message by message and answer by answer the answers were received, each the target of the
      sample row at its seed (`sampleStep`, OnBytes/Slice/BlkSendRun.lean), and NO ROUND WAS CLOSED
    BEHIND THEM; - a round named "LOC" was closed, whose entry has the old code's range and at least
      one position; it drew D.dL, which holds no element;
    - what is returned names the target, the oracle messages that take kept rows and the others by
      their places in the sending, and has the positions drawn;
    - the old rows were read at these positions: D.y; the claims were admitted.
  `csSigmaVerify_ran`: a run on a view has such a record.
Limits: nothing on what the reading of the old rows or the admission have done. Nothing on a dry
run. What a sample row's coefficients are is not said. Nothing on soundness.

-/
import OnBytes.Tie.Pv.Switch.LocRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice

/-- What a run of the switch has taken of a view and has made on its way. -/
structure LocTaken where
  /-- how the oracle messages sent are placed in trees -/
  lay    : TreeLay
  /-- the numbers of the oracle messages sent -/
  ids    : Array Nat
  /-- the shapes of the sampled ones -/
  shapes : List OracleShape
  /-- what the round of the seed drew -/
  dS     : Fmt.Drawn
  /-- the seeds cut out of it -/
  seeds  : List SampleSeed
  /-- the old rows' code -/
  code   : Code
  /-- what the round of the positions drew -/
  dL     : Fmt.Drawn
  /-- the plan's entry of that round -/
  eL     : Fmt.Entry
  /-- the symbols read -/
  y      : Array E
  /-- the contexts: after the receiving; after the round of the seed; after the last answer; after
  the round of the positions; after the reading; the same with intermediate values kept -/
  c0 : Ctx
  c1 : Ctx
  cA : Ctx
  cB : Ctx
  cC : Ctx
  cD : Ctx

/-- What holds of the record of a run. -/
structure LocRan (old : SingleRows) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice)
    (out : Switched) (c c' : Ctx) (D : LocTaken) : Prop where
  checked  : switchTargetCheck c.st old T = true
  laid     : layTrees c.st.codes (sentAll T others) = some D.lay
  sizes    : c.st.oracles.size = c.book.place.size
  numbers  : D.ids = (Array.range (sentAll T others).size).map (· + c.st.oracles.size)
  received : D.c0 = { c with
    ch := { c.ch with roots := c.ch.roots + D.lay.shapes.size }
    st := stSent c.st (sentAll T others)
    book := bookSent c (sentAll T others) D.lay }
  sampled  : (todoOf D.c0.st D.ids).mapM (fun o => (D.c0.st.oracles[o]?).map (·.shape)) =
    some D.shapes
  seedRound : (Blk.close "SEND seed" .seeds (D.shapes.foldl (fun a s => max a s.answers) 0)).Yields
    D.c0 D.dS D.c1
  seedsCut : Send.seedsOf (D.shapes.foldl (fun b s => max b (Send.cube D.c0.st.codes s).bits) 0)
    (D.shapes.foldl (fun a s => max a s.answers) 0) (D.dS.elems.map E.ofTriple) = some D.seeds
  notZero  : (D.seeds.all fun s => !isZeroE s.beta) = true
  answers  : RunFold (sampleStep D.c0.st D.seeds) ((todoOf D.c0.st D.ids).zip D.shapes) PUnit.unit
      D.c1
    PUnit.unit D.cA
  oldCode  : c.st.codes.base[old.code]? = some D.code
  locRound : (Blk.close "LOC" .positions).Yields D.cA D.dL D.cB
  locEntry : D.cB.ch.last = some D.eL ∧ D.eL.logN = D.code.logN ∧ 0 < D.eL.poss
  noElem   : D.dL.elems.map E.ofTriple = []
  returned : out = { g := D.ids.getD 0 noId, kept := D.ids.extract 1 (1 + T.kept.size),
                     others := D.ids.extract (1 + T.kept.size) D.ids.size,
                     positions := Positions.ofDraws D.code.logN D.dL.poss }
  read     : (singleRowsRead old out.positions).Yields D.cB D.y D.cC
  notes    : Blk.SameButNotes D.cC D.cD
  admitted : (switchAdmit old T gp out D.y).Yields D.cD () c'

/-- A run of the switch on a view has its record. -/
theorem csSigmaVerify_ran (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (csSigmaVerify old T gp others).Yields c out c') :
    ∃ D, LocRan old T gp others out c c' D := by
  obtain ⟨ids, cA, code, dL, eL, cB, y, cC, cD, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩
      :=
    csSigmaVerify_inv old T gp others out c c' h
  obtain ⟨c0, r1, r2⟩ := sendVerify_inv _ _ _ _ _ k2
  obtain ⟨lay, l1, l2, l3, l4⟩ := receiveOracles_inv _ _ _ _ hd r1
  have hd0 : c0.ch.dry = false := by
    rw [l4]
    exact hd
  obtain ⟨shapes, dS, seeds, c1, c2, v1, v2, v3, v4, v5, v6⟩ := verify_inv _ _ _ _ hd0 r2
  have e2 : cA = c2 := v6
  subst e2
  exact ⟨⟨lay, ids, shapes, dS, seeds, code, dL, eL, y, c0, c1, cA, cB, cC, cD⟩,
    ⟨k1, l1, l2, l3, l4, v1, v2, v3, v4, v5, k3, k4, ⟨k5, k6, k7⟩, k8, k9, k10, k11, k12⟩⟩

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.csSigmaVerify_ran
