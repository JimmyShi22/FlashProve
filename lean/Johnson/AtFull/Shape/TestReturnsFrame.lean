-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TestReturnsFrame.lean: THE PROXIMITY TEST ON THE REQUEST's GROUP (the kind K12)
AT ITS SEAT IN THE PROOF FILE's OWN FIRST CHAIN (member 354 of the flat list), IN THE FRAME's OWN
FORM: `Returns` (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), one of the premises of the rule
for acceptance (`accepted_of_shape`, the same file). Under the head `P5J.AtMgA`; general in the
three public files (in the goals' scope); a joining of laws; nothing is evaluated.

WHAT IT IS WORTH, FIRST. Under the guard, the step's own tests on rounds and columns and three
marks, the test on values `valsK12` IS EQUIVALENT TO THE SUB-PROTOCOL's OWN ACCEPT
(`k12_accept_iff_six`, Johnson/Desc/K12/Honest/Shape/TestFinishSix.lean): "returns" at this member
spares all form and nothing of the algebra: that the honest side's values pass is another premise.

A BAD RESULT. AT THE ONE HONEST FULL-SIZE RUN THAT HAS BEEN EVALUATED `testV` SAYS NO (Lean's
evaluator on one proof over made-up weights; an evaluation, no theorem). There the guard accepts;
`valsK12` and two of the three marks accept; the third mark, "no row taken in has a written-out
factor", says no at one row of the 659 taken in. So the rule's premise `Values` at 354 is not met by
that run at this test: the law beneath (`finish_returns_six_B`) asks of the state in front more than
that honest state gives. It stays true, and idle there.

Main names.
* `want_of_rounds`, `shown_of_rounds`, `fits_of_rounds`: what a block's step asks of rounds and
  columns, and what it shows its decision, hang on the block's rounds alone.
* `test_member_at`: the member b at number 354 states the kind's own rounds, and where the test at
  the finish (`atFinish`, Johnson/Desc/K12/AtFinish.lean) returns a state, b returns that state: the
  seat's guards on the mark and on the reply pass, since the finish's way out turns the statement,
  the book and the count of roots alone.
* `testGuardB p a`: THE GUARD, ON THE CHAIN's SHAPE ALONE: no mark; no count of rows waits; the
  chain stands at its finish; and the six clauses of `guardFinish` (TestFinishSix.lean) at the
  shape's core, the finish's group and the first fold's mask.
* `enter_of_guard`: where the guard accepts at a state's shape, the finish's way in returns, and
  `guardFinish` accepts at what it returns.
* `testV p s rs gs`: THE TESTS ON VALUES: `valsFinishSixB` (three marks and `valsK12`) at what the
  way in returns; TRUE where the way in refuses: that it returns is the guard's to say, not these
  tests'.
* `test_returns_frame`: `Returns` at 354, for every ft, G and vals UNDER THE PREMISE hGV: where G
  354 returns at a state's shape and vals 354 accepts, the guard and `testV` accept. A STEP THAT
  DOES NOT ASK THE GUARD NEED NOT MEET hGV: of `testGS` (TestAtHead.lean) no law says that its
  return gives the guard.
* `test_returns_guarded`: the guard in front of the step: G 354 = `optE` of "if the guard accepts
  then f, else nothing", for ANY f; vals 354 = `testV`. (That `Carries` is kept:
  `carries_behind_guard`, Johnson/AtFull/Shape/FrameNarrow.lean.)
* `test_returns_vals`: the guard among the tests: ANY G; vals 354 = the guard at the state's shape
  and `testV`. ON THIS ROAD vals 354 IS FALSE WHEREVER THE WAY IN REFUSES OR A CLAUSE OF THE GUARD
  SAYS NO: the rule's premise `Values` ends in vals and has no premise on G: so whoever proves
  `Values` at 354 then has to prove the whole guard from the thread.

Limits. THAT THE GUARD ACCEPTS AT THE SHAPE IN FRONT OF MEMBER 354 ON AN HONEST RUN IS SHOWN BY NO
THEOREM (it was seen to accept at the one run named above); with the guard in front of the step it
belongs to "the run on shapes returns". It reads the test's numbers `H2U.p12OfMade Zp.made`; under
the head these are the written member `H2K.Member.piLFull`, a closed term (`p12_at_head`,
TestNumbersAtHead.lean; that law takes the smaller head AtMg, which AtMgA gives). test_returns_frame
unfolds testV and calls finish_returns_six_B, as TestFinishSix.lean's finish_returns_idle does for
valsOrIdleB. THE RULE ASKS BESIDES, at this member, `FitsAt` and `Values`; `Carries` at every
member; the run on shapes; and that every first state at a valid input has the first shape: none of
these is here. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed`
accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named
sets of public files, in a side library. One tree at the first stage; the mask has come earlier; no
row taken in has a written-out factor (TestFinishSix.lean's Limits stand). `claimsB` reads values;
`stTidyB` reads values at one spot. G and vals are letters. At the format's second hash function.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TestAtHead
import Johnson.AtFull.Shape.FrameNarrow
import Johnson.Desc.K12.Honest.Shape.TestFinishSix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain OpenedColumn noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Ground.Sh (coreSh)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts atFinish enterFinish T12 P12)
open ProofFile.Honest (Returns returns_seat)
open ProofFile.Honest.Sh (guardFinish valsFinishSixB finish_returns_six_B)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 Two blocks with the same rounds -/

section
variable {S₁ S₂ C₁ C₂ : Type} {a : Block S₁ C₁} {b : Block S₂ C₂}

/-- The columns that a step wants. -/
theorem want_of_rounds (e : a.rounds = b.rounds) (ft : Nat) (rs : List Fmt.RoundView) :
    a.want ft rs = b.want ft rs := by
  unfold Block.want
  rw [e]

/-- The groups of columns that a step shows its decision. -/
theorem shown_of_rounds (e : a.rounds = b.rounds) (ft : Nat) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) : a.shown ft rs cols = b.shown ft rs cols := by
  unfold Block.shown
  rw [want_of_rounds e, e]

/-- The step's own tests on rounds and columns. -/
theorem fits_of_rounds (e : a.rounds = b.rounds) {ft : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (h : a.Fits ft rs cols) : b.Fits ft rs cols := by
  unfold Block.Fits at h ⊢
  rw [← want_of_rounds e, ← e]
  exact h

end

/-! ## 2 The seat -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Where the test at the finish returns a state, the member at 354 returns that state**; and it
states the kind's own rounds. -/
theorem test_member_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[354]? = some b ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).rounds ∧
      ∀ (s s' : S) rs gs, (atFinish (H2U.p12OfMade Zp.made)).decide s rs gs = .ok s' →
        b.decide s rs gs = .ok s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, b', eb, -, rfl, la⟩, -, -⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 1 b eb
  have hy := IM.yes_alone la (by intro k; cases k)
  refine ⟨_, q, ?_, fun s s' rs gs hd => (hy s s' rs gs).2 ⟨hd, ?_, ?_⟩⟩
  · rw [la]
    rfl
  · obtain ⟨o, t', -, -, hf, -, rfl⟩ :=
      VerifiableInference.Desc.K12.Seat.atFinish_ok _ s s' rs gs hd
    show s.failed = none
    cases e : s.failed with
    | none => rfl
    | some m => rw [e] at hf; cases hf
  · obtain ⟨o, t', -, -, -, -, rfl⟩ :=
      VerifiableInference.Desc.K12.Seat.atFinish_ok _ s s' rs gs hd
    simp [ProofFile.sameReply]

/-! ## 3 The guard on the shape, the tests on values -/

/-- **The guard**, on the chain's shape alone. -/
def testGuardB (p : P12) (a : ChainSh) : Bool :=
  !a.marked &&
    (match a.rowsOwed with
      | none => true
      | some n => n == 0) &&
    a.fin.any fun f => guardFinish p a.core f.fr.group f.mask

/-- **The tests on values**, at the structure that the finish's way in lays; true where it lays
none. (Sign for sign the imported TestFinishSix.lean's valsOrIdleB; no theorem joins the two names.)
-/
def testV (p : P12) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  match enterFinish s with
  | .ok t => valsFinishSixB p t rs gs
  | .error _ => true

/-- **Where the guard accepts at a state's shape, the way in returns**, and the test's own guard
accepts at what it returns. -/
theorem enter_of_guard {p : P12} {s : S} (hg : testGuardB p (chainSh s) = true) :
    ∃ t, enterFinish s = .ok t ∧
      guardFinish p (coreSh ⟨t.st, t.book, t.roots⟩) t.g t.mask = true := by
  unfold testGuardB at hg
  rw [Bool.and_eq_true, Bool.and_eq_true] at hg
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  have hw : (⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ : S).noneWaits = true := h2
  have hf : failed.isNone = true := by
    have h1' : (!failed.isSome) = true := h1
    cases failed with
    | none => rfl
    | some e => cases h1'
  cases here with
  | fin o =>
    refine ⟨⟨st, book, roots, o.fr.group, .nothing, o.mask⟩, ?_, h3⟩
    unfold enterFinish
    simp only [hw, hf, VerifiableInference.Desc.need]
    rfl
  | _ => cases h3

/-! ## 4 The frame -/

/-- **THE PROXIMITY TEST's MEMBER, IN THE FRAME's FORM: "RETURNS"**, under hGV: where the step at
354 returns at a state's shape and the tests at 354 accept, the guard and `testV` accept. -/
theorem test_returns_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (ft : Nat)
    (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hGV : ∀ s u rs gs, G 354 (shA s) = .ok u → vals 354 s rs gs = true →
      testGuardB (H2U.p12OfMade Zp.made) (chainSh s) = true ∧
        testV (H2U.p12OfMade Zp.made) s rs gs = true) :
    Returns cF.blocksInOrder ft (firstZA G vals) 354 := by
  obtain ⟨b, hb, hr, hd⟩ := test_member_at h
  refine returns_seat hb fun rs cols hF s u hg hv => ?_
  obtain ⟨g1, v⟩ := hGV s u _ _ hg hv
  obtain ⟨t, he, g2⟩ := enter_of_guard g1
  unfold testV at v
  rw [he] at v
  have v' : valsFinishSixB (H2U.p12OfMade Zp.made) t (rs.map noDigest) (b.shown ft rs cols) =
    true := v
  rw [shown_of_rounds hr] at v' ⊢
  obtain ⟨s', hs'⟩ := finish_returns_six_B he g2 ft rs cols (fits_of_rounds hr hF) v'
  exact ⟨s', hd s s' _ _ hs'⟩

/-- The guard in front of the step; any step behind it. -/
theorem test_returns_guarded (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (ft : Nat)
    (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (f : ShA → Option ShA)
    (hG : G 354 = optE fun y =>
      if testGuardB (H2U.p12OfMade Zp.made) y.1 then f y else none)
    (hV : vals 354 = testV (H2U.p12OfMade Zp.made)) :
    Returns cF.blocksInOrder ft (firstZA G vals) 354 := by
  refine test_returns_frame h ft G vals fun s u rs gs hg hv => ⟨?_, by rw [← hV]; exact hv⟩
  rw [hG] at hg
  have k := optE_ok.1 hg
  by_cases c : testGuardB (H2U.p12OfMade Zp.made) (shA s).1 = true
  · exact c
  · rw [if_neg c] at k
    cases k

/-- The guard among the tests; any step. On this road the tests at 354 say no wherever the way in
refuses or a clause of the guard does. -/
theorem test_returns_vals (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (ft : Nat)
    (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hV : vals 354 = fun s rs gs =>
      testGuardB (H2U.p12OfMade Zp.made) (chainSh s) && testV (H2U.p12OfMade Zp.made) s rs gs) :
    Returns cF.blocksInOrder ft (firstZA G vals) 354 := by
  refine test_returns_frame h ft G vals fun s u rs gs _ hv => ?_
  rw [hV] at hv
  exact Bool.and_eq_true_iff.1 hv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.want_of_rounds
#print axioms Johnson.AtFull.Shape.shown_of_rounds
#print axioms Johnson.AtFull.Shape.fits_of_rounds
#print axioms Johnson.AtFull.Shape.test_member_at
#print axioms Johnson.AtFull.Shape.enter_of_guard
#print axioms Johnson.AtFull.Shape.test_returns_frame
#print axioms Johnson.AtFull.Shape.test_returns_guarded
#print axioms Johnson.AtFull.Shape.test_returns_vals
#print axioms Johnson.AtFull.Shape.testGuardB
#print axioms Johnson.AtFull.Shape.testV
