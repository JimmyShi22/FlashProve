-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BattK6Frames.lean: TWO MEMBERS OF THE PROOF FILE's OWN FIRST CHAIN IN THE FORM
THAT THE THREAD's FRAME ASKS (ProofFile.Honest.Carries | Returns at firstZA g vals,
Johnson/AtFull/Shape/FrameForm.lean): member 355 (K13's front, batching and step in front of W) and
member 341 (the output head's own rounds). Under the head P5J.AtMgA; a joining of laws; nothing is
evaluated.
  **`batt_frame`**: for every g with g 355 = liftO (battGS (K13.whereOf Zp)) and every vals: Carries
    and Returns at 355. No test on values is asked.
  `k6V W s`: the two tests on the state beyond its shape at the head's own rounds, as one test with
    code: the state's own test on the request's words (startOk), and the head's text's own test on
    the lookup's points, as it is typed in given (Johnson/Desc/Kinds/HeadFrame.lean).
  **`k6_frame`**: for every g with g 341 = liftO (k6GR (At.X Zp).hS) and every vals with vals 341 s
    rs gs = k6V (At.X Zp) s: Carries and Returns at 341.
By batt_at (BattAtHead.lean), k6_step_at (K6StepAtHead.lean), carries_of_seat | returns_of_seat
(FrameForm.lean), ProofFile's returns_seat (Johnson/Desc/ProofFile/Honest/Thread/ShapeJoin.lean), liftO_ok
(FrameOpt.lean), the library's pointsOk_of_test (Johnson/Desc/Kinds/Law/FromGiven.lean).
Limits. The steps g and the tests vals are letters with an equation at one number each: no table of
all 358 is built here. At 341 "carries" is under the step's own return, and k6GR's tests are enough,
not shown to be needed. k6V READS THE STATE BEYOND ITS SHAPE, AND SAYS NO WHERE THE LOOKUP's RECORD
IS NOT LAID: whoever pays the values at 341 owes that it is laid there. That arm is a choice of this
text: k6_step_at asks the test on the points only of a record that is there. Of k6V's test on the
points the half on sizes could be read off the shape (K6StepAtHead.lean's Limits). UNDER THE HEAD:
that it has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). No state is shown by a theorem at
which a step returns. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or
hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.AtFull.Shape.BattAtHead
import Johnson.AtFull.Shape.K6StepAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Kinds.Head (parOf startOk)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns carries_seat returns_seat)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The frame's two premises at member 355** (K13's front, batching and step in front of W): no
test on values is asked. -/
theorem batt_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder[355]?).isSome = true ∧
      ∀ (ft : Nat) g vals,
        g 355 = liftO (battGS (VerifiableInference.Desc.K13.whereOf Zp)) →
        Carries cF.blocksInOrder ft (firstZA g vals) 355 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 355 := by
  obtain ⟨b, q, hrd, hc, hr⟩ := batt_at h
  refine ⟨by rw [q]; rfl, fun ft g vals hg => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u _ hd hu => ?_
    rw [hg] at hu
    obtain ⟨w, hw, rfl⟩ := liftO_ok.1 hu
    obtain ⟨e1, e2⟩ := hc s _ gs t hd
    have hw' : battGS (VerifiableInference.Desc.K13.whereOf Zp) (chainSh s) = some w := hw
    rw [e1] at hw'
    obtain rfl := Option.some.inj hw'
    show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
    rw [e2]
  · refine returns_of_seat q fun s rs gs u hfit hu _ => ?_
    rw [hg] at hu
    obtain ⟨w, hw, -⟩ := liftO_ok.1 hu
    rw [hrd] at hfit
    exact hr s rs gs w hw hfit

/-- The two tests on the state beyond its shape at the output head's own rounds, as one test with
code: the state's own test on the request's words; the head's text's own test on the lookup's
points. WHERE NOTHING WAS HEARD OF THE LOOKUP (s.lookHeard? = none) IT SAYS NO. -/
def k6V (W : Model.Verify.Public) (s : S) : Bool :=
  startOk W s && (match s.lookHeard? with
    | some g =>
      letI := (parOf W.hS (workOf W)).sizes
      (VerifiableInference.Desc.Kinds.Head.fromLookup (parOf W.hS (workOf W)).floor g.zx
          fun c => g.zk.getD c #[]).calls.zipIdx.all fun c =>
        (g.zk.getD c.2 #[]).size ==
            VerifiableInference.Desc.Kinds.Head.lJ (parOf W.hS (workOf W)).floor c.1.2 +
              VerifiableInference.Desc.Kinds.Norm.lt &&
          VerifiableInference.Desc.Kinds.Point.last (g.zk.getD c.2 #[])
              (VerifiableInference.Desc.Kinds.Norm.ls + VerifiableInference.Desc.Kinds.Norm.lt) ==
            VerifiableInference.Desc.Kinds.Point.last g.zx
              (VerifiableInference.Desc.Kinds.Norm.ls + VerifiableInference.Desc.Kinds.Norm.lt)
    | none => false)

/-- **The frame's two premises at member 341** (the output head's own rounds). -/
theorem k6_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder[341]?).isSome = true ∧
      ∀ (ft : Nat) g vals,
        g 341 = liftO (k6GR (P5J.At.X Zp).hS) →
        (∀ s rs gs, vals 341 s rs gs = k6V (P5J.At.X Zp) s) →
        Carries cF.blocksInOrder ft (firstZA g vals) 341 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 341 := by
  obtain ⟨b, q, hc, hr⟩ := k6_step_at h
  refine ⟨by rw [q]; rfl, fun ft g vals hg hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u _ hd hu => ?_
    rw [hg] at hu
    obtain ⟨w, hw, rfl⟩ := liftO_ok.1 hu
    obtain ⟨e1, e2⟩ := hc s _ gs t w hd hw
    subst e1
    show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
    rw [e2]
  · refine returns_seat q fun rs cols hF s u hu hvv => ?_
    have hu' : g 341 (shA s) = .ok u := hu
    rw [hg] at hu'
    obtain ⟨w, hw, -⟩ := liftO_ok.1 hu'
    have hvv' : vals 341 s (rs.map noDigest) (b.shown ft rs cols) = true := hvv
    rw [hv] at hvv'
    unfold k6V at hvv'
    rw [Bool.and_eq_true] at hvv'
    refine hr s ft rs cols w hw hvv'.1 (fun g0 hg0 => ?_) hF
    have h2 := hvv'.2
    rw [hg0] at h2
    exact @VerifiableInference.Desc.Kinds.Head.Law.Came.pointsOk_of_test
      (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes _ _ _ h2

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.batt_frame
#print axioms Johnson.AtFull.Shape.k6_frame
#print axioms Johnson.AtFull.Shape.k6V
