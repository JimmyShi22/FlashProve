-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorsByShape.lean

What it defines. Two state functions for the shared chain's two proximity tests, doorUF and
doorOmegaF: doorOf (JobShared.lean) over the same blocks, from the same first state and by the same
way in as doorU and doorOmega (NearAtHead.lean), with another fall-back: a state that is made of the
shape that the plan gives, fallU (ShapeBehind.lean) and fallOmega. The jobs jobAtU and jobAtOmega
(JobShared.lean) take any state function as an argument, so nothing of JobShared.lean or
NearAtHead.lean turns.

What it proves. At every input and whatever precedes the test, whatever the readers of the key and
of the columns are: the shape of doorUF's state is the term Shape.doorU (endOf Q sentU), and the
shape of doorOmegaF's state is the term Shape.doorO (endOmega Q sentU p): no premise on a fall-back.
Where the three tests that read the rows hold at the fall-back, they hold at the state function's
state; where the part that layFits reads of the fall-back is the plan's, it is the plan's at the
state function's state.

Names.
  endOmega   the shape behind the test on G_u: the library's testCore at the core of endOf; the
      core of endOf where testCore returns nothing.
  fallOmega, shape_fallOmega   what the seat of the test on G_omega enters at the lift of that
      shape.
  doorUF, doorOmegaF   the two state functions.
  shape_doorUF, shape_doorOmegaF   the shapes.
  three_doorUF, three_doorOmegaF   the three tests, from the fall-back's.
  near_doorUF, near_doorOmegaF   the part that layFits reads, from the fall-back's.

By what. shape_door_U_fall, three_door_U, three_door_Omega, prop_doorOf (MarksAtDoor.lean);
shape_behind_nine (ShapeBehind.lean); near_at_U, near_at_Omega, pubNear_doorOf (PubNear.lean);
door_enterO (Johnson/Desc/K14/Shape/Door.lean); sh2_lift (Up.lean); early_of_planOk,
answers_of_planOk (Johnson/Desc/K12/Law/Top.lean).

Limits.
- The premises on the two fall-backs (the three tests; the part that layFits reads) are Bools on
  terms of the plan. They are evaluated at no plan here.
- Where testCore returns nothing at the plan's term, endOmega is not the shape of any state behind
  the test on G_u; shape_doorOmegaF then speaks of the fall-back alone, for the fold cannot return
  there.
- That the state on entry is the verifier's is not shown: where the fold does not return, doorOf
  gives the fall-back. Whether it returns hangs on the reader cols. The eight in front of the test
  on G_u read columns of one stored table alone ("LOC"), which a reader can make of the input
  (colsLoc, DoorReturns.lean). From the test on G_u on, the blocks read columns of trees that parts
  of the run have sent; a part is handed no opened column, so no reader of this type makes them: at
  the test on G_omega the fold fails at every honest run.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.MarksAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts Seat.enter Seat.onGu)
open Desc.K14 (P14 St blocks first withU withOmega)
open Desc.K14.Shape (Sh2 lift sh2_lift doorO door_enterO)
open ProofFile.Honest.Sh (testSh testCore)

variable {W X : Type}

/-- **The shape behind the test on G_u, a term of the plan.** -/
def endOmega (Q : P14) (sentU : Array OracleNotice) (p : P12) : Sh2 :=
  { core := (testCore p (endOf Q sentU).core (endOf Q sentU).lin.gU
      (endOf Q sentU).lin.firstMask).getD (endOf Q sentU).core
    lin := (endOf Q sentU).lin }

/-- A state of that shape, made of the shape alone: what the seat of the test on G_omega enters at
the lift of the term. -/
def fallOmega (Q : P14) (sentU : Array OracleNotice) (p : P12) : T12 :=
  { st := (lift (endOmega Q sentU p)).st, book := (lift (endOmega Q sentU p)).book
    roots := (lift (endOmega Q sentU p)).roots, g := (lift (endOmega Q sentU p)).loc.gOmega
    pass := .nothing, mask := none }

theorem shape_fallOmega (Q : P14) (sentU : Array OracleNotice) (p : P12) :
    testSh (fallOmega Q sentU p) = doorO (endOmega Q sentU p) := by
  have h := door_enterO (lift (endOmega Q sentU p)) (fallOmega Q sentU p) rfl
  rw [h, sh2_lift]

/-- The state function at the test on G_u, with the fall-back made of the plan's shape. -/
def doorUF (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit)) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) : W → Front X → T12 :=
  doorOf bs (fun w => first Q.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols
    (fallU Q sentU)

/-- The state function at the test on G_omega, behind bs and the test on G_u at the parameters p,
with the fall-back made of the plan's shape. -/
def doorOmegaF (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit)) (p : P12)
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn) : W → Front X → T12 :=
  doorOf (bs ++ [Seat.onGu (proximityTestKind guardedProximityTestParts p)]) (fun w => first Q.codes (key w))
    (Seat.enter (·.gOmega) fun _ => none) cols (fallOmega Q sentU p)

/-- **The shape of doorUF's state is one term of the plan.** -/
theorem shape_doorUF (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (sentU : Array OracleNotice)
    (hw : withU Q.S = some sentU) (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    testSh (doorUF Q sentU bs key cols w fr) = Desc.K14.Shape.doorU (endOf Q sentU) :=
  shape_door_U_fall Q bs hb hS sentU hw key cols w fr

/-- **The shape of doorOmegaF's state is one term of the plan.** -/
theorem shape_doorOmegaF (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (sentU : Array OracleNotice)
    (hw : withU Q.S = some sentU) (p : P12)
    (hpU : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    testSh (doorOmegaF Q sentU bs p key cols w fr) = doorO (endOmega Q sentU p) :=
  prop_doorOf (fun t => testSh t = doorO (endOmega Q sentU p)) _ _ _ cols _
    (shape_fallOmega Q sentU p)
    (fun w _ x t hx ht => by
      obtain ⟨c, hc, e⟩ := shape_behind_nine Q bs hb sentU hw hS p
        (H2K.JointK.early_of_planOk p hpU) (H2K.JointK.answers_of_planOk p hpU) 0 (key w) _ _ x t
        hx ht
      rw [e]
      unfold doorO endOmega
      rw [hc]
      rfl) w fr

/-- The three tests at doorUF's state, from the fall-back's. -/
theorem three_doorUF (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (hS : Q.S.sharedSplitNeeded = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (hf : Three (fallU Q sentU))
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    Three (doorUF Q sentU bs key cols w fr) :=
  three_door_U Q bs hb hp hS sentU hw key cols _ hf w fr

/-- The three tests at doorOmegaF's state, from the fall-back's. -/
theorem three_doorOmegaF (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (hS : Q.S.sharedSplitNeeded = true)
    (hM : Q.S.masksAhead = true) (sentU : Array OracleNotice) (hw : withU Q.S = some sentU)
    (hl : Q.codes.lengthsOk = true) (p : P12)
    (hpU : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (hf : Three (fallOmega Q sentU p))
    (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    Three (doorOmegaF Q sentU bs p key cols w fr) :=
  three_door_Omega Q bs hb hp hS hM sentU hw hl p hpU key cols _ hf w fr

/-- The part that layFits reads of doorUF's state is the plan's, where it is so at the fall-back. -/
theorem near_doorUF (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU)
    (hf : pubNear (fallU Q sentU) = nearOf (pubBehind Q sentU) 0) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubNear (doorUF Q sentU bs key cols w fr) = nearOf (pubBehind Q sentU) 0 :=
  pubNear_doorOf _ _ _ cols _ _ hf
    (fun w _ x t hx ht => near_at_U Q bs hb hS hM sentU hw (key w) _ _ x t hx ht) w fr

/-- The same at doorOmegaF's state. -/
theorem near_doorOmegaF (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (hM : Q.S.masksAhead = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (p : P12)
    (hpU : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (hf : pubNear (fallOmega Q sentU p) = nearOf (pubBehind Q sentU) 1) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubNear (doorOmegaF Q sentU bs p key cols w fr) = nearOf (pubBehind Q sentU) 1 :=
  pubNear_doorOf _ _ _ cols _ _ hf
    (fun w _ x t hx ht => near_at_Omega Q bs hb hS hM sentU hw p hpU (key w) _ _ x t hx ht) w fr

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.endOmega
#print axioms ProofFile.Honest.K12.Light.fallOmega
#print axioms ProofFile.Honest.K12.Light.shape_fallOmega
#print axioms ProofFile.Honest.K12.Light.doorUF
#print axioms ProofFile.Honest.K12.Light.doorOmegaF
#print axioms ProofFile.Honest.K12.Light.shape_doorUF
#print axioms ProofFile.Honest.K12.Light.shape_doorOmegaF
#print axioms ProofFile.Honest.K12.Light.three_doorUF
#print axioms ProofFile.Honest.K12.Light.three_doorOmegaF
#print axioms ProofFile.Honest.K12.Light.near_doorUF
#print axioms ProofFile.Honest.K12.Light.near_doorOmegaF
