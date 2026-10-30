-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/HandedWide.lean: the statements of good_at and hand_at (Row.lean) under the
wider condition on the book (BookClearAny), and the implications that lead to them from
Spec.goodSeatedWide. It claims no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has.
  Spec.goodHandedWide   The statement of good_at (Row.lean), without its hypothesis Hr, with
                        BookClear replaced by BookClearAny. Let σ₀ be a side that Side.seated
                        returns for the sender's row sendRow a J ("our row"), let its sub-protocol
                        have K1's two rounds and oracle messages at J.P, and let the book satisfy
                        BookClearAny at (a, 0). Then σ₀ has Good at On := True and the bound budAt,
                        with the predicates A and B that never hold, so that plays and acc hold
                        vacuously.
  Spec.handHandedWide   The statement of hand_at (Row.lean), without Hr, with the same replacement.
                        Under the same premises every side of the row, with the rule's predicates
                        substituted (Unlettered.lay), has Good for some A₁ and B₁; the two that
                        never hold serve.
  goodHandedWide_of     Proved here: Spec.goodSeatedWide implies Spec.goodHandedWide.
  handHandedWide_of     Proved here: Spec.goodHandedWide implies Spec.handHandedWide, through
                        hand_of_house.
The two under Spec are statements only; proved as goodHandedWide and handHandedWide in
HandedWideProofs.lean.

Limits.
Where the premises of the two statements are met. That the book which the maker onlineProverFromPublicFiles returns
satisfies BookClearAny at the opening's sender, at the returned description's own order of places,
is proved in the side library, in scope, where the gate accepts (clear_at_opening,
AtFullSide/K1/BookAtOpening.lean); the rest: the table of premises in Johnson/SendSim/Defs.lean,
"the book is clear". That the side at our row's place has K1's rounds and oracle messages is proved,
if the maker (ProofFile.onlineDescription) succeeds, at the places of K1's own lot on the first chain
(roundsAt_own, AtDescHand.lean, with own_of_job, AtDescStands.lean). The two statements are all or
nothing: one address that does not satisfy SpenderClearAny makes them vacuous.
Both hold at predicates A and B that never hold, so the fields plays and acc hold vacuously.
The implications have named propositions as premises, which this file does not prove, so it proves
no equation between distributions by itself.

How it fits. BookClearAny and Spec.goodSeatedWide are in Johnson/SendSim/At/BookWide.lean,
hand_of_house in Johnson/Desc/ProofFile/Honest/Thread/RowsMore.lean. What the rule requires of a row
is the second form. good_at and hand_at (Row.lean) have it only under BookClear: at an owner one of
whose spenders takes the coefficients of a table of two rows that is sent along, they are vacuous.
AtDescHand.lean applies the second statement at the first segment's opening. No main theorem rests
on them: Spec.fieldsAtLots uses sendFreshAtWide (HandedWideProofs.lean) directly.
-/
import Johnson.SendSim.Seat.Row
import Johnson.SendSim.At.BookWide

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At

/-- States that a side that Side.seated returns for the sender's row (sendRow a J), and whose
sub-protocol has K1's two rounds and oracle messages at J.P, has the structure Good, at On := True
and the bound budAt, at every book that satisfies BookClearAny at the address (a, 0), with
predicates A and B that never hold, so that plays and acc hold vacuously. Statement only; proved as
goodHandedWide in Johnson/SendSim/Seat/HandedWideProofs.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt.
-/
def Spec.goodHandedWide : Prop :=
  ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (S Cl V W X Pb : Type) (φ : Face V W Pb) (bs : List (Block S Cl)) (a : Place)
    (J : SendJob W X) (fs₀ : List (Fall S)) (σ₀ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (chain ft : Nat),
    Side.seated bs (sendRow (V := V) (Pb := Pb) a J).place (sendRow a J).row fs₀ = some σ₀ →
    σ₀.block.rounds = K1.rounds J.P → σ₀.block.oracles = K1.oracles J.P →
    BookClearAny J.P J.ride Bk ord ⟨a, 0⟩ →
    Good pre φ σ₀ Bk ord chain ft (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (sendRow (V := V) (Pb := Pb) a J).On (sendRow (V := V) (Pb := Pb) a J).bud

/-- States that, under the premises of Spec.goodHandedWide, every side of the sender's row (sendRow
a J) with the rule's predicates substituted (Unlettered.lay) has Good for some A₁ and B₁; the two
that never hold serve, so plays and acc hold vacuously. Statement only; proved as handHandedWide in
Johnson/SendSim/Seat/HandedWideProofs.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
def Spec.handHandedWide : Prop :=
  ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (S Cl V W X Pb : Type) (φ : Face V W Pb) (bs : List (Block S Cl)) (a : Place)
    (J : SendJob W X) (fs fs₀ : List (Fall S)) (σ₀ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (chain ft : Nat) (T : W → Thread Bk S Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop),
    Side.seated bs (sendRow (V := V) (Pb := Pb) a J).place (sendRow a J).row fs₀ = some σ₀ →
    σ₀.block.rounds = K1.rounds J.P → σ₀.block.oracles = K1.oracles J.P →
    BookClearAny J.P J.ride Bk ord ⟨a, 0⟩ →
    ∀ σ, ((sendRow (V := V) (Pb := Pb) a J).lay T Sd bs).side bs fs = some σ →
      ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ ((sendRow a J).lay T Sd bs).On
        ((sendRow a J).lay T Sd bs).bud

/-- Spec.goodSeatedWide implies Spec.goodHandedWide. The premise is proved as goodSeatedWide in
Johnson/SendSim/Seat/HandedWideProofs.lean. -/
theorem goodHandedWide_of (H : At.Spec.goodSeatedWide) : Spec.goodHandedWide :=
  fun pre S Cl V W X Pb φ _ _ J _ σ₀ Bk ord chain ft hσ hr ho hB =>
    H pre S Cl V W X Pb φ σ₀ J Bk ord chain ft (seated_at hσ hr ho)
      (by rw [place_of_seated hσ]; exact hB)

/-- Spec.goodHandedWide implies Spec.handHandedWide, through hand_of_house. The premise is proved as
goodHandedWide in Johnson/SendSim/Seat/HandedWideProofs.lean. -/
theorem handHandedWide_of (H : Spec.goodHandedWide) : Spec.handHandedWide :=
  fun pre S Cl V W X Pb φ bs a J _ fs₀ σ₀ Bk ord chain ft T Sd hσ hr ho hB =>
    hand_of_house (sendRow a J) T Sd hσ
      (H pre S Cl V W X Pb φ bs a J fs₀ σ₀ Bk ord chain ft hσ hr ho hB)

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.goodHandedWide_of
#print axioms OnBytes.SendSim.Seat.handHandedWide_of
#print axioms OnBytes.SendSim.Seat.Spec.goodHandedWide
#print axioms OnBytes.SendSim.Seat.Spec.handHandedWide
