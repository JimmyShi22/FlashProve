-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LaterAccepted.lean: THE KIND K1's DIGITS' MEMBER ALONE: THE
DEBT AcceptedS OF A THREAD (Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) at a member that is
that sub-protocol, seated alone: general in the thread T, in Said, in the fall and in the member's
number. One statement: calls.

  k1_later_acceptedS: by later_seated_yes (Johnson/Desc/ProofFile/Honest/K1/Law/LaterSeated.lean)
    and the frame's own laws on a member's step: steps_one_half
    (Johnson/Desc/ProofFile/Honest/Law/Thread.lean), chainSteps_rows
    (Johnson/Desc/ProofFile/Honest/Law/Steps.lean), fits_played and step_iff_decide
    (Johnson/Desc/ProofFile/Honest/Law/Cut.lean): the rounds as played fit the declared rounds, and
    the step accepts at just the columns laid where the decision returns. NEITHER A STOP NOR A FALL
    IS SPENT.

WHO PAYS THE PREMISES. member, four clauses on the thread's member number b: it is the digits'
sub-protocol seated alone (for the description's own chain: IM.k1_later, Johnson/IMR/K1Seat.lean) ·
its place is not of the kind K7 · the honest side's list has a half at its place · that half has as
many rounds as the member: the last two are on the thread's list of halves: its maker's; the fourth
is no more than a test that the laying of the member's steps makes itself: where it fails no step is
laid and the debt asks nothing. front, from the thread in front and what is said to the state: no
mark, and THE COMMITMENT's STEP ON THE SHAPE OF THE STATE RETURNS.

Limits. ONE OF THE KIND's FOUR SORTS OF MEMBER. THE WEIGHT LIES IN front's SECOND HALF (commitG,
Johnson/Desc/First/Shape/Commit.lean): that it returns at any state is shown nowhere: so the debt is
paid here at no thread. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LaterSeated
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.Steps
import Johnson.Desc.K15.SendOwnLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place KindName roundsFit regroup groupsOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (commitG chainSh)

variable {q : Params.First} {gp : _root_.Desc.Plain.GPar} {link piece moment : Nat}
  {arrays : Option (List Nat)} {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **AcceptedS AT THE SEATED DIGITS' MEMBER**, under one premise from the thread in front to the
state. -/
theorem k1_later_acceptedS (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (fall : Nat → S → List Fmt.Drawn → Option String)
    (b : Nat)
    (member : ∀ blk, T.bs[b]? = some blk → ∃ name a g,
      IM.LaidAlone ProofFile.sameReply blk
        (VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays : Block S Unit).retype
        name a ∧ a.kind ≠ KindName.K7 ∧
      (T.hs.find? fun g => g.place == blk.place) = some g ∧ g.rounds = blk.rounds.length)
    (front : ∀ k s m E, ThrS T Said b k s m E → s.failed = none ∧
      ∃ t, commitG (VerifiableInference.Desc.K1.parLater q gp link piece moment) link moment arrays
        (chainSh s) = some t) :
    AcceptedS T Said fall b := by
  intro blk hblk k s m E ds y cols hA hd _ _ hM
  obtain ⟨name, a, g, hla, hk, hf, hr⟩ := member blk hblk
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM'
  have ho := (chainSteps_rows [blk] T.hs l hl).1 blk (List.mem_singleton.2 rfl)
  obtain ⟨c, -, rfl⟩ := steps_one_half hf hl
  obtain ⟨h0, t, hg⟩ := front k s m E hA
  have hF := (fits_played hr ho hy hd hc).1.1
  rw [IM.alone_rounds hla] at hF
  obtain ⟨s', hs'⟩ := later_seated_yes hla hk
    (gs := regroup ((groupsOf T.ft blk.rounds ds).map (·.length)) cols) h0
    ((VerifiableInference.Desc.roundsFit_noDigest _ _).trans hF) hg
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hM, (step_iff_decide s s' hr ho hy hd hc).2 hs'⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_later_acceptedS
