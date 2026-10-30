-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/SeatYes.lean: THE CLOSING OF A SEGMENT (K10): WHEN THE VERY BLOCK THAT THE
DESCRIPTION SEATS SAYS YES: BOTH WAYS: at the first chain's state. Lemmas on the verifier's own
text; no honest side's frame in them; none of the library's goals.

The seated term is `IM.seatedAs ProofFile.sameReply (K9.closing Q).retype name a`
(Johnson/IMR/SeatForm.lean; that it stands at each link l < 25, under premises and at one hash
alone: Johnson/Desc/K10/Honest/KeepsSeat.lean, over another author's law).

  `turns_of_step`     the library's own relation `K10Step` gives `K10Turns` (Keeps.lean)
    `closing_yes_iff`   the lifted block's decision says yes at t just if the kind's own does at
                   `K9.recOf t`. THE LIBRARY's IS STRONGER, with the state behind: `lift_decide_iff`
                   (First/Close/Law/PieceOf.lean), `Block.lift_decide`
                   (Johnson/Desc/RunLaws.lean): not called
  `seated_yes_iff`    THE SEATED TERM's DECISION SAYS YES AT t JUST IF t bears no mark of failure,
                      there are 2 + k rounds of the kind's shape, and the two tests of
                      Johnson/Desc/K10/Honest/Split.lean say yes of `K9.recOf t`
  `seated_fits_iff`   the step's own tests in front of the decision (`Block.Fits`) at the seated
                      term ARE: 2 + k rounds of the kind's shape
    `seated_step_iff`   THE SEATED TERM's STEP SAYS YES JUST IF: the same

THE GUARDS OFF THE SEATED TERM are opened by hand in the proofs; the library has them as laws, at
an address that is not of the kind K7: `IM.yes_alone`, `IM.step_alone`, `IM.alone_rounds`
(Johnson/IMR/SeatForm.lean): not called.

Limits. WHICH STATE STANDS BEHIND stays under "there is": that is `seated_keeps` (KeepsSeat.lean).
The block's tests on the plan are read by neither decision nor step. At the lot's own type of
claims, retyped. It stands over files of this folder (Fits.lean, KeepsSeat.lean and what lies
beneath them). No member is called here (Johnson/Desc/K10/Honest/AtChainToy.lean calls
`seated_yes_iff`; `seated_step_iff` has none). AtChainToy.lean STANDS OVER THIS FILE AND OVER
OTHER AUTHORS' FILES: a tree may hold this file without it: what this head says of it is then said
of no file of that tree. At the seat's own test `ProofFile.sameReply` (the way from the tests to the yes
spends that the closing leaves what the chain puts out as it was). Shown of no honest run. Nothing
on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Fits
import Johnson.Desc.K10.Honest.KeepsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)

/-- The library's own relation "t' is K10's writing at a yes of the frame's closing at what
K10 reads of t" (`K10Step`, Johnson/Desc/First/Close/Law/AsksOfMg.lean) gives `K10Turns`. -/
theorem turns_of_step {t t' : S} (h : K10Step t t') : K10Turns t t' := by
  obtain ⟨es, rs, x, hx, rfl⟩ := h
  unfold K10Turns
  rw [recOf_put]
  exact ⟨closeFrame_keeps hx, rfl⟩

/-- The lifted block's decision, opened. -/
theorem closing_decide {Cl : Type} (Q : Par) (t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (K9.closing (Cl := Cl) Q).decide t rs gs =
      (((kind (Cl := Cl)) Q).decide (K9.recOf t) rs gs).map (K9.putRec t) := rfl

/-- The lifted block's decision says yes at t just if the kind's own does at the record of t. -/
theorem closing_yes_iff {Cl : Type} (Q : Par) (t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (∃ t', (K9.closing (Cl := Cl) Q).decide t rs gs = .ok t') ↔
      ∃ r, ((kind (Cl := Cl)) Q).decide (K9.recOf t) rs gs = .ok r := by
  rw [closing_decide]
  cases ((kind (Cl := Cl)) Q).decide (K9.recOf t) rs gs with
  | ok r => exact ⟨fun _ => ⟨r, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | error e => exact ⟨fun ⟨_, h⟩ => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩

/-- **THE SEATED TERM's DECISION SAYS YES JUST IF** the state bears no mark, the rounds are 2 + k
of the kind's shape, and both tests say yes of the state's record. -/
theorem seated_yes_iff (Q : Par) (name : String) (a : Place) (t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (∃ t', (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).decide t rs gs =
        .ok t') ↔
      t.failed = none ∧ rs.length = 2 + Q.k ∧ ShapedAll rs ∧ closeShapeB Q (K9.recOf t) = true ∧
        closeValsB (K9.recOf t) rs = true := by
  constructor
  · rintro ⟨t', h⟩
    have hk := seated_keeps _ _ _ h
    have inner : ∃ u, (K9.closing (Cl := Unit) Q).decide t rs gs = .ok u := by
      have key : ∀ u, (IM.marked (K9.closing (Cl := Unit) Q).retype name).decide t rs gs = .ok u →
          ∃ u, (K9.closing (Cl := Unit) Q).decide t rs gs = .ok u := fun u hu =>
        ⟨u, (ProofFile.Law.guardMark_yes.1
          (show (ProofFile.guardMark (K9.closing (Cl := Unit) Q).retype).decide t rs gs = _ from hu)).1⟩
      unfold IM.seatedAs Block.guarded at h
      simp only at h
      split at h
      · exact key _ h
      · obtain ⟨u, hu, _⟩ := ok_bind h
        exact key _ hu
    exact ⟨(keeps_unmarked hk).2,
      (close_yes_split (Cl := Unit) Q _ rs gs).1 ((closing_yes_iff Q t rs gs).1 inner)⟩
  · rintro ⟨hm, hl, hs, h1, h2⟩
    obtain ⟨r, hr⟩ := (close_yes_split (Cl := Unit) Q (K9.recOf t) rs gs).2 ⟨hl, hs, h1, h2⟩
    have d0 : (K9.closing (Cl := Unit) Q).decide t rs gs = .ok (K9.putRec t r) := by
      rw [closing_decide, hr]
      rfl
    have hk : (K9.putRec t r).failed = none := (putRec_keeps t r).2.2.1.trans hm
    have d1 : (IM.marked (K9.closing (Cl := Unit) Q).retype name).decide t rs gs =
        .ok (K9.putRec t r) :=
      ProofFile.Law.guardMark_yes.2 ⟨d0, hk⟩
    refine ⟨K9.putRec t r, ?_⟩
    unfold IM.seatedAs Block.guarded
    simp only
    split
    · exact d1
    · show ((IM.marked (K9.closing (Cl := Unit) Q).retype name).decide t rs gs).bind _ = _
      rw [d1]
      show seatSame ProofFile.sameReply t (K9.putRec t r) = _
      unfold seatSame
      rw [if_pos]
      show ProofFile.sameReply t (K9.putRec t r) = true
      unfold ProofFile.sameReply
      rw [(putRec_keeps t r).2.2.2.1]
      simp

/-- **The step's own tests at the seated term** are the kind's block's: 2 + k rounds of the kind's
shape. -/
theorem seated_fits_iff (Q : Par) (same : S → S → Bool) (name : String) (a : Place) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (IM.seatedAs same (K9.closing (Cl := Unit) Q).retype name a).Fits ft rs cols ↔
      rs.length = 2 + Q.k ∧ ShapedAll rs :=
  fits_iff (Cl := Unit) Q ft rs cols

/-- **THE SEATED TERM's STEP SAYS YES JUST IF** the state bears no mark, the rounds are 2 + k of
the kind's shape, and both tests say yes of the state's record. -/
theorem seated_step_iff (Q : Par) (name : String) (a : Place) (ft : Nat) (t : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) :
    (∃ t' n, (IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).step ft t rs
        cols = .ok (t', n)) ↔
      t.failed = none ∧ rs.length = 2 + Q.k ∧ ShapedAll rs ∧ closeShapeB Q (K9.recOf t) = true ∧
        closeValsB (K9.recOf t) rs = true := by
  rw [← vals_noDigest (K9.recOf t) rs]
  constructor
  · rintro ⟨t', n, h⟩
    obtain ⟨h1, h2, _⟩ := (step_iff ft _ t t' rs cols n).1 h
    obtain ⟨a1, a2⟩ := (seated_fits_iff Q _ name a ft rs cols).1 h1
    obtain ⟨b1, _, _, b4, b5⟩ := (seated_yes_iff Q name a t _ _).1 ⟨t', h2⟩
    exact ⟨b1, a1, a2, b4, b5⟩
  · rintro ⟨b1, a1, a2, b4, b5⟩
    obtain ⟨t', h2⟩ := (seated_yes_iff Q name a t (rs.map noDigest)
      ((IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype name a).shown ft rs cols)).2
      ⟨b1, by rw [List.length_map, a1], shapedAll_noDigest a2, b4, b5⟩
    exact ⟨t', _, (step_iff ft _ t t' rs cols _).2
      ⟨(seated_fits_iff Q _ name a ft rs cols).2 ⟨a1, a2⟩, h2, rfl⟩⟩

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.turns_of_step
#print axioms ProofFile.Honest.K10.YesFree.closing_yes_iff
#print axioms ProofFile.Honest.K10.YesFree.seated_yes_iff
#print axioms ProofFile.Honest.K10.YesFree.seated_fits_iff
#print axioms ProofFile.Honest.K10.YesFree.seated_step_iff
