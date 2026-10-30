-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeParts.lean: the closing of a segment (K10): the lot's job makes the group's rows,
and they pass the public test `rowsFit`, from one named premise for each stage of the job's text.

  `rows_of_parts`   the job's rows return, from the two tests in front, the last segment, the three public tests of
                    `jobRows` and the shared text's return
  `made_of_parts`   so the field made of `CarryOwed` (Honest/K10/Xch/CarryTop.lean), at one input, list of challenges and
                    carried coins

Limits. Every stage is a premise here. The statement is an implication: it says nothing on whether the stages hold.
-/
import Johnson.Desc.ProofFile.Honest.K10.Thr.HalfOfLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (SegmentPub GroupRows Stretch groupRowsOf ownReady ownBy freshTable segmentsOf)

variable {W₀ Rc Xi Tr : Type}

/-- The segments that the lot's job at numbers Q reads. -/
abbrev lotSegs (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) : List SegmentPub := (segmentsOf Z G).take (Q.link + 1)

/-- The main rows that the lot's job reads, at an input and a list of challenges. -/
abbrev lotOwn (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par)
    (w : Local W₀ Rc Xi Tr) (front : List Fmt.Drawn) : Nat → Nat → Nat → Nat → Cb.Gl.E :=
  ownBy (rows w.x) (readers w) (addrsAt Z G)
    (fun s m => ((((lotSegs Z G Q)[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) front

/-- What the job returns of the shared text's rows. -/
abbrev rowsOut (S : SegmentPub) (R : GroupRows) : GroupData :=
  ⟨S.sizes.codes, S.sizes.code, S.sizes.maskCode, (R.members.zip R.rows).map fun x => memberOf x.1 x.2⟩

/-- **The job's rows return, stage by stage.** -/
theorem rows_of_parts (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (w : Local W₀ Rc Xi Tr) (front : List Fmt.Drawn)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Z G Q).pub)) {S : SegmentPub} {R : GroupRows}
    (hReady : ownReady (rows w.x) G.first.layout (askPlace (addrsAt Z G)) (lotSegs Z G Q) front = .ok ())
    (hHeard : heardAll (lotSegs Z G Q) front = .ok ())
    (hLast : (lotSegs Z G Q).getLast? = some S)
    (hKnown : segsKnown (lotSegs Z G Q) = true)
    (hRoomy : segsRoomy (lotSegs Z G Q) = true)
    (hRuns : (borneAt Z Q).length = runsAsked (lotSegs Z G Q))
    (hRows : groupRowsOf freshTable (lotSegs Z G Q) (lotOwn readers rows Z G Q w front) front
      (Stretch.carried _ ca) = .ok R) :
    (lotJob readers rows stAt Z G Q).rows w front ca = .ok (rowsOut S R) := by
  show (ProofFile.Honest.K2.ownReady (rows w.x) G.first.layout (askPlace (addrsAt Z G)) (lotSegs Z G Q) front).bind
    (fun _ => (heardAll (lotSegs Z G Q) front).bind fun _ =>
      (jobBare (addrsAt Z G) (lotSegs Z G Q) (fun i => i.st Q) ⟨Q, borneAt Z Q⟩).rows
        (closeIn readers rows stAt w) front ca) = _
  rw [hReady]
  show (heardAll (lotSegs Z G Q) front).bind (fun _ =>
      (jobBare (addrsAt Z G) (lotSegs Z G Q) (fun i => i.st Q) ⟨Q, borneAt Z Q⟩).rows
        (closeIn readers rows stAt w) front ca) = _
  rw [hHeard]
  show (jobBare (addrsAt Z G) (lotSegs Z G Q) (fun i => i.st Q) ⟨Q, borneAt Z Q⟩).rows
        (closeIn readers rows stAt w) front ca = _
  unfold jobBare jobRows
  simp only [hLast, hKnown, hRoomy, hRuns, Bool.not_true, Bool.false_eq_true, if_false, bne_self_eq_false]
  show Except.map _ (groupRowsOf freshTable (lotSegs Z G Q) (lotOwn readers rows Z G Q w front) front
    (Stretch.carried _ ca)) = _
  rw [hRows]
  rfl

/-- **The field made, from one premise for each stage.** -/
theorem made_of_parts (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (w : Local W₀ Rc Xi Tr) (front : List Fmt.Drawn)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Z G Q).pub)) {S : SegmentPub} {R : GroupRows}
    {St : OnBytes.Statement} {Gp : OnBytes.Group}
    (hReady : ownReady (rows w.x) G.first.layout (askPlace (addrsAt Z G)) (lotSegs Z G Q) front = .ok ())
    (hHeard : heardAll (lotSegs Z G Q) front = .ok ())
    (hLast : (lotSegs Z G Q).getLast? = some S)
    (hKnown : segsKnown (lotSegs Z G Q) = true)
    (hRoomy : segsRoomy (lotSegs Z G Q) = true)
    (hRuns : (borneAt Z Q).length = runsAsked (lotSegs Z G Q))
    (hRows : groupRowsOf freshTable (lotSegs Z G Q) (lotOwn readers rows Z G Q w front) front
      (Stretch.carried _ ca) = .ok R)
    (hFit : rowsFit St Gp (rowsOut S R) = true) :
    ∃ R', (lotJob readers rows stAt Z G Q).rows w front ca = .ok R' ∧ rowsFit St Gp R' = true :=
  ⟨_, rows_of_parts readers rows stAt Z G Q w front ca hReady hHeard hLast hKnown hRoomy hRuns hRows, hFit⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.rows_of_parts
#print axioms ProofFile.Honest.K10.made_of_parts
