-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescHand.lean: at the first segment's opening of the proof file's
description, the statement that Side.seated returns a side for the sender's row (sendRow, "our
row"), and that every such side has the field fits, ExactAt and the field fresh of Good, the last
two for queried positions within the bound, if the maker (ProofFile.onlineDescription) succeeds, the first segment
is not of the kind .head, and the book is clear at the opening's sender (BookClearAny); and the same
in the form of the rule's premise. It claims no property of the protocol: not hiding, not zero
knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The premises of both statements: IM.Open (the maker has succeeded); the public
part has a segment number 0, and it is not of the kind .head; and the book satisfies BookClearAny
("clear") at the opening's sender. They hold for every face, wit, first, D, order, chain number and
first-tree number.
  Spec.fieldsAtFirst    The main statement. Side.seated returns a side from F.first.blocksInOrder for our row
                        at the opening (openRow), and every such side has fits, exact (ExactAt) and
                        fresh (FreshAt).
  Spec.handAtFirst      The same in the form that the rule's premise hand₁ requires of one row. The
                        row, with the rule's predicates substituted (Unlettered.lay), has a side,
                        and every such side has Good for some A₁ and B₁. It says no more than the
                        main statement: the two predicates that never hold serve as A₁ and B₁.
  roundsAt_own          Proved here, pointwise. Under IM.Open, the side that Side.seated returns
                        from F.first.blocksInOrder at the place of a sub-protocol of K1's own lot at the
                        ground Bs.G₀ has that sub-protocol's rounds and oracle messages.
  handAtFirst_of        Proved here: Spec.handHandedWide implies Spec.handAtFirst.
  handAtFirst_of_fields   Proved here: Spec.fieldsAtFirst implies Spec.handAtFirst. So the second
                        says no more than the first.
The two under Spec are statements only. Spec.fieldsAtFirst follows from Spec.fieldsAtLots
(fieldsAtFirst_of_lots, AtDescLots.lean), which is proved (fieldsAtLots, AtDescLotsProof.lean);
Spec.handAtFirst follows from Spec.fieldsAtFirst (handAtFirst_of_fields, here).

Limits.
  - The premise on the book stays. At the book that the maker onlineProverFromPublicFiles returns, at the returned
    description's own order of places, it is proved in the side library, in scope, where the gate
    accepts (clear_at_opening, AtFullSide/K1/BookAtOpening.lean); that the book is the right one for
    an honest execution is neither a premise nor a conclusion.
  - The statements give three fields of five. Nothing is said on the other two fields of Good: plays
    (the parts can be played with the coins that the book gives them) and acc (the verifier
    accepts).
  - The statements are all or nothing: one address that does not satisfy SpenderClearAny makes them
    vacuous, also for ExactAt, which reads no book.
  - The bound on queried positions is a premise inside exact and fresh. That the positions queried
    in an execution are within it is not proved here. Where each premise is proved for the release's
    files: the table of premises in Johnson/SendSim/Defs.lean.
  - That the job fits its place (sendFits) is not a premise. Where it does not fit, what is
    disclosed is the error value on both sides of both equations: exact then says nothing, and fresh
    then speaks only of the sender's coins.
  - The two premises on the public part serve only to find a member at the opening's place, and
    stands_at_job (AtDescStands.lean) finds one from IM.Open, without them.
  - The ground is the maker's own, Bs.G₀, at a request of zeros. Whoever has another ground must
    connect the two.
  - There is one owner, and one row of the chain: the rule requires the same of every other row.
  - wit (how the input is read), first (the number of the first new oracle message) and D (the data)
    are free variables. Nothing says which wit, first and D are the honest prover's. In
    Spec.handAtFirst the parameters T and Sd are not read.
  - That the maker succeeds at given public files is not proved here (see the Limits of
    AtDesc.lean).
  - No equation between distributions is proved in this file: the two implications have named
    propositions as premises.

How it fits. AtDesc.lean ends in Seated at the description's own members; Spec.handHandedWide
(HandedWide.lean) takes a side's rounds and oracle messages. This file joins the two at one place.
The same at a segment's reads and digits and at the request's own table is Spec.fieldsAtLots
(AtDescLots.lean), which implies Spec.fieldsAtFirst without using that statement's two premises on
the public part (fieldsAtFirst_of_lots). So this file is the earlier, narrower form; no other file
takes its two statements as a premise.

The other names. openRow: our row at the opening, sendRow at the place of openJob and at the job
jobOver (openJob …) wit.
-/
import Johnson.SendSim.Seat.AtDescSome
import Johnson.SendSim.Seat.HandedWide

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open ProofFile.Honest.AtPlace (of_find)

variable {V W X Xi Pb : Type}

/-- If the maker has succeeded (IM.Open), the side that Side.seated returns from the description's
first chain at the place of a sub-protocol b₀ of K1's own lot at the ground Bs.G₀ has b₀'s rounds
and oracle messages. -/
theorem roundsAt_own {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) {b₀ : Block First.S Unit}
    (hown : b₀ ∈ (ProofFile.k1Pure Z).own Bs.G₀) {a : Place}
    {row : List (ProofFile.Honest.Part V W X × Sim Pb)} (hpl : b₀.place = a)
    {fs₀ : List (Fall F.S₁)} {σ₀ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder a row fs₀ = some σ₀) :
    σ₀.block.rounds = b₀.rounds ∧ σ₀.block.oracles = b₀.oracles := by
  have e := O.desc
  subst e
  obtain ⟨hm, hp⟩ := of_find (find_of_seated hσ)
  exact member_of_own O hown hm (hp.trans hpl.symm)

/-- Our row at the opening: the honest sender at the job jobOver (openJob …) wit, with its
simulator. -/
abbrev openRow (Z : ProofFile.Pub) (G : ProofFile.Ground) (wit : W → PlaceIn Xi) (first : Nat)
    (D : RowDataOf Xi) : Unlettered V W X Pb :=
  sendRow (openJob (X := X) Z G first D).P.place (jobOver (openJob (X := X) Z G first D) wit)

/-- States: if the maker has succeeded (IM.Open), the public part has a segment number 0, that
segment is not of the kind .head, and the book satisfies BookClearAny at the opening's sender, then
Side.seated returns a side from the description's first chain for our row at the opening, and every
such side has the field fits, ExactAt and the field fresh. Statement only; it follows from
Spec.fieldsAtLots (fieldsAtFirst_of_lots, AtDescLots.lean). -/
def Spec.fieldsAtFirst : Prop :=
  ∀ (V W X Xi Pb : Type) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (_ : IM.Open o pol lay KL F Z Bs base c A B) (sub : First.ModelPart)
    (_ : (ProofFile.subsOf Z)[0]? = some sub) (_ : sub ≠ .head) (φ : Face V W Pb)
    (wit : W → PlaceIn Xi) (first : Nat) (D : RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain ft : Nat) (fs : List (Fall F.S₁)),
    BookClearAny (openJob (X := X) Z Bs.G₀ first D).P (openJob (X := X) Z Bs.G₀ first D).ride Bk ord
      ⟨(openJob (X := X) Z Bs.G₀ first D).P.place, 0⟩ →
    (∃ σ : Side F.S₁ F.Cl V W X Pb, Side.seated F.first.blocksInOrder
        (openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).place
        (openRow Z Bs.G₀ wit first D).row fs = some σ) ∧
      ∀ σ : Side F.S₁ F.Cl V W X Pb, Side.seated F.first.blocksInOrder
          (openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).place
          (openRow Z Bs.G₀ wit first D).row fs = some σ →
        σ.fits = true ∧
          ExactAt φ σ chain ft (openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).On
            (openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).bud ∧
          FreshAt φ σ Bk ord (openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).bud

/-- States, under the premises of Spec.fieldsAtFirst: our row at the opening, with the rule's
predicates substituted (Unlettered.lay), has a side, and every such side has Good for some A₁ and
B₁. It follows from fits, ExactAt and FreshAt (good_of_fields); it says less than these: Good's
field exact is asked only where the opened columns are what the front holds for pre. The two
predicates that never hold serve as A₁ and B₁, so plays and acc hold vacuously. Statement only; it
follows from Spec.fieldsAtFirst (handAtFirst_of_fields, in this file).
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
def Spec.handAtFirst : Prop :=
  ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (V W X Xi Pb : Type) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (_ : IM.Open o pol lay KL F Z Bs base c A B) (sub : First.ModelPart)
    (_ : (ProofFile.subsOf Z)[0]? = some sub) (_ : sub ≠ .head) (φ : Face V W Pb)
    (wit : W → PlaceIn Xi) (first : Nat) (D : RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain ft : Nat) (T : W → Thread Bk F.S₁ F.Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop) (fs : List (Fall F.S₁)),
    BookClearAny (openJob (X := X) Z Bs.G₀ first D).P (openJob (X := X) Z Bs.G₀ first D).ride Bk ord
      ⟨(openJob (X := X) Z Bs.G₀ first D).P.place, 0⟩ →
    (∃ σ, ((openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).lay T Sd F.first.blocksInOrder).side
        F.first.blocksInOrder fs = some σ) ∧
      ∀ σ, ((openRow (V := V) (X := X) (Pb := Pb) Z Bs.G₀ wit first D).lay T Sd F.first.blocksInOrder).side
          F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁
          ((openRow Z Bs.G₀ wit first D).lay T Sd F.first.blocksInOrder).On
          ((openRow Z Bs.G₀ wit first D).lay T Sd F.first.blocksInOrder).bud

/-- Spec.handHandedWide implies Spec.handAtFirst. The premise is proved as handHandedWide in
Johnson/SendSim/Seat/HandedWideProofs.lean. -/
theorem handAtFirst_of (H : Spec.handHandedWide) : Spec.handAtFirst := by
  intro pre V W X Xi Pb o pol lay KL F Z Bs base c A B O sub h0 hh φ wit first D Bk ord chain ft T
    Sd fs hB
  obtain ⟨σ₀, hσ, -⟩ := seatedAt_first_some (V := V) (X := X) (Pb := Pb) O h0 hh wit first D fs
  obtain ⟨hr, ho⟩ := roundsAt_own O (own_first Z Bs.G₀) rfl hσ
  exact ⟨⟨σ₀, hσ⟩, H pre _ _ V W X Pb φ F.first.blocksInOrder _
    (jobOver (openJob (X := X) Z Bs.G₀ first D) wit) fs fs σ₀ Bk ord chain ft T Sd hσ hr ho hB⟩

/-- Spec.fieldsAtFirst implies Spec.handAtFirst: the form that the rule requires says no more than
the three fields. -/
theorem handAtFirst_of_fields (H : Spec.fieldsAtFirst) : Spec.handAtFirst := by
  intro _ V W X Xi Pb o pol lay KL F Z Bs base c A B O sub h0 hh φ wit first D Bk ord chain ft T Sd
    fs hB
  obtain ⟨⟨σ₀, hσ₀⟩, h⟩ := H V W X Xi Pb o pol lay KL F Z Bs base c A B O sub h0 hh φ wit first D Bk
    ord chain ft fs hB
  refine ⟨⟨σ₀, hσ₀⟩, fun σ hσ => ?_⟩
  obtain ⟨hf, he, hfr⟩ := h σ hσ
  exact ⟨_, _, good_of_fields hf he hfr⟩

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.roundsAt_own
#print axioms OnBytes.SendSim.Seat.handAtFirst_of
#print axioms OnBytes.SendSim.Seat.handAtFirst_of_fields
#print axioms OnBytes.SendSim.Seat.openRow
#print axioms OnBytes.SendSim.Seat.Spec.fieldsAtFirst
#print axioms OnBytes.SendSim.Seat.Spec.handAtFirst
