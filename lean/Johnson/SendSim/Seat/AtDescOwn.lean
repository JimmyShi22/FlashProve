-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescOwn.lean: wherever the maker returns (IM.Open), at the place of any
sub-protocol of K1's own lot the proof file's description has a member. For every job with that
sub-protocol's place, rounds and oracle messages, every side that Side.seated returns there for our
row has the fields fits and exact of Good, and fresh if the book is clear (BookClearAny). It claims
no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The premise is IM.Open. Let b₀ be a sub-protocol of K1's own lot (ProofFile.k1Pure Z
at the ground Bs.G₀), and J any job with b₀'s place, rounds and oracle messages.
  fields_of_seated   Proved here, given Spec.sendExactAt and Spec.sendFreshAtWide as hypotheses
                     (both are theorems elsewhere). A side that is Seated at a job has fits; exact,
                     for every chain number and number of the first tree; and fresh, for every book
                     and order at which the book is clear at that sender.
  Spec.fieldsAtOwn   Side.seated returns a side at J's place for our row. Every side that it returns
                     there has fits and exact; no book is mentioned. If a book is clear at that
                     sender, the side has fresh at that book. The statement holds for every such J,
                     whatever its other fields; the lot's own jobs are among them (own_of_job,
                     AtDescStands.lean). Proved as fieldsAtOwn in AtDescLotsProof.lean.
  fieldsAtOwn_of     Spec.sendExactAt and Spec.sendFreshAtWide imply Spec.fieldsAtOwn. Both are
                     theorems: sendExactAt (Johnson/SendSim/At/ExactAt.lean) and sendFreshAtWide
                     (Johnson/SendSim/Seat/HandedWideProofs.lean).

How it fits. This file speaks of any sub-protocol of the lot and any matching job. AtDescLots.lean
speaks of the jobs of the honest sides lotSide and wSide, row by row as the rule asks, and also
covers the request's own table. Both rest on member_at_own (AtDescStands.lean), seatedAt_own
(AtDesc.lean) and fields_of_seated. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits. All limits of AtDescLots.lean hold here too. In addition:
The premises fix J's place, rounds and oracle messages. They do not fix how many random symbols each
code appends to a row (the field r of a code), which tables are sent along, the number of the first
new message or the data. So a caller can apply the statement at a job that is not one of lotSide's;
the conclusion then speaks of the sender at that job.
The sending of the request's own table is in another lot (K13.lot4) and is not covered here.
-/
import Johnson.SendSim.Seat.AtDescStands
import Johnson.SendSim.Seat.AtDescHand

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

/-- A side that is Seated at a job has fits and exact; and fresh at every book that is clear at the
sender. The two premises are statements that are proved elsewhere. -/
theorem fields_of_seated (He : At.Spec.sendExactAt) (Hf : At.Spec.sendFreshAtWide)
    {S Cl V W X Pb : Type} (φ : Face V W Pb) {σ : Side S Cl V W X Pb} {J : SendJob W X}
    (h : Seated σ J) (chain ft : Nat) :
    σ.fits = true ∧
      ExactAt φ σ chain ft (fun _ _ _ _ => True) (fun _ _ asks => budAt J.P asks) ∧
      ∀ (Bk : ProverCoinCounts) (ord : List Place), BookClearAny J.P J.ride Bk ord ⟨σ.block.place, 0⟩ →
        FreshAt φ σ Bk ord fun _ _ asks => budAt J.P asks :=
  ⟨h.fits, He S Cl V W X Pb φ σ J chain ft h, fun Bk ord hB => Hf S Cl V W X Pb φ σ J Bk ord h hB⟩

/-- Statement only; proved as fieldsAtOwn in AtDescLotsProof.lean. Where the description's maker
returns: at the place of a sub-protocol of K1's own lot, beside our row at a job with that
sub-protocol's place, rounds and oracle messages, a side is found; every side found there has fits
and exact; and if a book is clear at that sender, it has fresh at that book. -/
def Spec.fieldsAtOwn : Prop :=
  ∀ (V W X Xi Pb : Type) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (_ : IM.Open o pol lay KL F Z Bs base c A B) (b₀ : Block First.S Unit)
    (_ : b₀ ∈ (ProofFile.k1Pure Z).own Bs.G₀) (J : SendJob (PlaceIn Xi) X)
    (_ : b₀.place = J.P.place) (_ : b₀.rounds = K1.rounds J.P) (_ : b₀.oracles = K1.oracles J.P)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (chain ft : Nat) (fs : List (Fall F.S₁)),
    (∃ σ : Side F.S₁ F.Cl V W X Pb, Side.seated F.first.blocksInOrder
        (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
        (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs = some σ) ∧
    ∀ σ : Side F.S₁ F.Cl V W X Pb, Side.seated F.first.blocksInOrder
        (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
        (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs = some σ →
      σ.fits = true ∧
        ExactAt φ σ chain ft (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).On
          (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).bud ∧
        ∀ (Bk : ProverCoinCounts) (ord : List Place), BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
          FreshAt φ σ Bk ord (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).bud

/-- Spec.sendExactAt and Spec.sendFreshAtWide imply Spec.fieldsAtOwn. -/
theorem fieldsAtOwn_of (He : At.Spec.sendExactAt) (Hf : At.Spec.sendFreshAtWide) :
    Spec.fieldsAtOwn := by
  intro V W X Xi Pb o pol lay KL F Z Bs base c A B O b₀ hown J hpl hr ho φ wit chain ft fs
  refine ⟨?_, fun σ hσ => ?_⟩
  · refine seated_of_member _ fs ?_
    have e := O.desc
    subst e
    obtain ⟨m, hm, hp⟩ := member_at_own O hown
    exact ⟨m, hm, hp.trans hpl⟩
  · obtain ⟨h1, h2, h3⟩ :=
      fields_of_seated He Hf φ (seatedAt_own O hown J wit hpl hr ho hσ) chain ft
    exact ⟨h1, h2, fun Bk ord hB => h3 Bk ord (by rw [place_of_seated hσ]; exact hB)⟩

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.fields_of_seated
#print axioms OnBytes.SendSim.Seat.fieldsAtOwn_of
