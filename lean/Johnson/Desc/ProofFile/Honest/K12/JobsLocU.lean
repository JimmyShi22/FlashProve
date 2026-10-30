-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/JobsLocU.lean

What it holds. The two jobs at the proximity test on G_u whose state functions read the committed
table's columns at "LOC"'s positions: the prover's (jobLocU) of the input, the simulators'
(simLocU), given the stored table's columns opened at "LOC"'s positions, of what a simulator is
given. And the clause door of the condition at the second part's entry (OnFreeT.door,
Sim/TreesExact.lean), letter by letter, at these two jobs, at a run of the frame's walking prover:
general in the description (door_clause_any).

Names.
  jobLocU, simLocU   the two jobs.
  door_clause_any    the clause.

By what. door_sim_any (DoorAnyRun.lean); the texts of jobAtU (JobShared.lean), ManyJob.toRun
(RunMany.lean), RunJob.toTest (RunJob.lean), restFront (Sim/Row.lean), the frame's Face.pub.

Limits.
- It is the clause door alone, of the eight of OnFreeT. The equation holds at the fall-back too:
  that the one state is what the seat's way in makes of the state that the description's fold
  returns is door_of_called's sentence (DoorAnyRun.lean), which asks besides: the eight by name;
  what goes out with o_u; that the blocks in front are, just nine, like the shared chain's front
  block and the eight; that the key is that of the fold's start.
- A, p, sentU, bs and st are free in the two definitions.
- The simulators' job is given the stored table's columns opened at "LOC"'s positions: these are
  computed from the weights and count against the committed tables' budget of columns
  (DoorSimAtRun.lean's head).
- simLocU's state function reads Before.stored: of that the frame's own text says that in a real run
  the values are the prover's own and depend on its input. What is read is said, and no more.
- Of the walk (runC), not of play (run); nothing on whether ready or runC returns, or whether the
  part is called. "The second part" is said by the number of rounds in front alone: σ and u are
  free.
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone.
- What MarksBehind.lean stands over are files of this library.
  Also beneath this file: K12/LiveField.lean and, of the frame's authors (ProofFile/Honest/): Blind,
  Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW, WalkHeard, WalkLive, WalkOpened,
  Law/WalkMid, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt, Law/Rule/OpenedStep.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAnyRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (P14 St readsAtLoc)
open Desc.K14.Honest (ReadsNone)
open ProofFile.Honest.K14 (SendPub)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt Face ready runC
  midSharedAtW storedShown srcOf)

/-- **The prover's job at the test on G_u whose state on entry is made of the stored table's
columns**: the typed job jobAtU (JobShared.lean); its state on entry is doorUF (DoorsByShape.lean)
with the reader colsLoc (DoorReturns.lean) at st, a function that makes the stored tables' columns
of the index and the stored tables' randomness (at a prover P: P.storedWords). The input is a shared
part's: index, randomness, key. All letters are free here. Where that state is off doorUF's
fall-back is shown elsewhere, under premises: door_of_called (DoorAnyRun.lean). -/
def jobLocU {W₀ Rc X : Type} (A : SendPub) (p : P12) (sentU : Array OracleNotice)
    (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X → ℕ → OnBytes.E)) :
    ManyJob (Common W₀ Rc TableKey) X :=
  jobAtU A p (doorUF A.P sentU bs (fun w => w.key)
    (fun w fr => colsLoc A.P (st w.w₀ w.rc) fr.seen.rounds)) weights rand u?

/-- **The simulators' job at the test on G_u, given the stored table's columns opened at "LOC"'s
positions**: the place's numbers; the first fold sends no fresh table of its own; the state on entry
is simDoorU (DoorSimAtRun.lean); the trees that the first round of positions opens are the place's
own first ones, named as madeSimsOpen (Sim/RestTiesAtHeadU.lean) names them. It has no input and no
coin among its letters; its state function reads of a front the rounds as a view shows them and
Before.stored at "LOC"'s positions, whose values in a real run are the prover's own. -/
def simLocU (Q : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit)) (p : P12)
    (chain : ℕ) : SimJob TableKey :=
  ⟨p, false, simDoorU Q sentU bs,
    p.nums.first.map fun x => ((srcOf chain x.2).1, (srcOf chain x.2).2, x.1.a)⟩

/-- **The clause door of OnFreeT (Sim/TreesExact.lean), letter by letter, at a run: general in the
description.** J: the test's job made of jobLocU at the prover's own stored columns. Js: simLocU,
given the stored table's columns opened at "LOC"'s positions. At the stand m in front of the test's
second part (S at i := the first part's number of rounds), where that part is called: J.rec₀ at the
stand's input and at the front as the second part's moves lay it (restFront) is Js.rec₀ at the
input's public part and at the run's own front, cut back by the first part's rounds.
Public: hpl, hpre. On the filling and the book: hR, S. On the run: hrun, hc. chain is read by
simLocU's list of trees alone, not by this clause.
It is the clause door alone. The equation holds whether or not the fold in front returns. Of the
walk (runC), not of play (run); nothing on whether runC returns or calls the part. -/
theorem door_clause_any {Xi W₀ Rc Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (A : SendPub) (p : P12) (sentU : Array OracleNotice) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E)) (chain : ℕ)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre t : List (Block F.S₂ F.Cl))
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t (firstLen p.nums.stages))
    (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry) (post : List Fmt.DeclaredRound)
    (h0 : ReadsNone d0) (h1 : ReadsNone d1) (h2 : ReadsNone d2)
    (hpre : pre.flatMap (·.rounds) =
      d0 :: d1 :: d2 :: { entry := e, stored := [readsAtLoc A.P.S.fold A.P.item] } :: post)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀,
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + firstLen p.nums.stages ∧
      (jobLocU A p sentU bs P.storedWords weights rand u?).toRun.toTest.rec₀ m.st.input
          (restFront (jobLocU A p sentU bs P.storedWords weights rand u?).toRun.toTest m) =
        (simLocU A.P sentU bs p chain).rec₀ (Face.shared.pub m.st.input)
          ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, u.number⟩).cut
              (firstLen
                (jobLocU A p sentU bs P.storedWords weights rand u?).toRun.toTest.p.nums.stages)) :=
    by
  obtain ⟨m, hm, hlen, hdoor⟩ := door_sim_any (X := X₀) hpl A.P sentU bs hR σ u pre t
    (firstLen p.nums.stages) S d0 d1 d2 e post h0 h1 h2 hpre hrun hc
  refine ⟨m, hm, hlen, ?_⟩
  refine hdoor (restFront (jobLocU A p sentU bs P.storedWords weights rand u?).toRun.toTest m) ?_
  show m.seen.take (m.seen.length - firstLen p.nums.stages) = _
  rw [hlen, Nat.add_sub_cancel]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.jobLocU
#print axioms ProofFile.Honest.K12.Light.simLocU
#print axioms ProofFile.Honest.K12.Light.door_clause_any
