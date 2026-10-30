-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshOwnerForm.lean: kind K14: WHAT THE LAW AT THE TEST
spOwnerTest (Honest/K14/FreshOwner.lean) CONCLUDES at a book, an order of places and an owner: the
letter Fresh of the frame's OwnerLaw (Honest/BookGuard.lean). Two definitions: propositions' forms.

  SpFresh         at every side that stands at the owner's place, whose row is the part at "send
                  o_omega" and whose sub-protocol declares the shared sending's rounds, and at every
                  bound that gives spBud: the field fresh of Good (Honest/Side.lean) at every
                  member, in the field's own form (FreshMember, Honest/Small/Field.lean)
  SpFreshSeated   the same at THE SIDE THAT Side.seated RETURNS at the owner's place off a list of
                  sub-protocols, where the row handed to it is the part: hr and hd are no premises

-/
import Johnson.Desc.ProofFile.Honest.K14.FreshDefs
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (FreshMember)

/-- **The field fresh of Good at every side that stands at the owner's place, whose row is the part
at "send o_omega" and whose sub-protocol declares the shared sending's rounds (hr, hd), at every
bound that gives spBud.** A definition: the form of a conclusion. IT IS CONDITIONAL ON THE SIDE: at
an address at which no such side stands it says nothing. -/
def SpFresh (A : SendPub) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Prop :=
  ∀ (S Cl X Pb W₀ Rc Ky : Type) (wit : Common W₀ Rc Ky → Ask) (sim : Sim Pb)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb),
    σ.row = [(liftSend wit (sendingPart (jobOmega A)), sim)] →
    σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega A).Q →
    SendDeclared σ.block (jobOmega A) → ({ place := σ.block.place, part := 0 } : Addr) = o →
    ∀ bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop,
      (∀ ds asks, bud 0 ds asks → spBud A asks) →
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u

/-- **The field fresh of Good at THE SIDE THAT THE FRAME's Side.seated RETURNS AT THE OWNER's
PLACE** off a list xs of sub-protocols, where the row that is handed to it is the part at "send
o_omega" beside any simulator; at every bound that gives spBud at the owner's number. A definition:
the form of a conclusion. hr and hd are no premises here: they are to be had from the list and the
place. OF o IT READS THE PLACE, AND THE NUMBER IN bud ALONE: the field reads the book at the side's
place and THE MEMBER's number. -/
def SpFreshSeated {Cl : Type} (P : Desc.K14.P14) (a : Nat)
    (xs : List (VerifiableInference.Desc.Block Desc.K14.St Cl)) (Bk : ProverCoinCounts) (ord : List Place)
    (o : Addr) : Prop :=
  ∀ (X Pb W₀ Rc Ky : Type) (wit : Common W₀ Rc Ky → Ask) (sim : Sim Pb)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (fs : List (Fall Desc.K14.St))
    (σ : Side Desc.K14.St Cl Empty (Common W₀ Rc Ky) X Pb),
    Side.seated xs o.place [(liftSend wit (sendingPart (jobOmega ⟨P, a⟩)), sim)] fs = some σ →
    ∀ bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop,
      (∀ ds asks, bud o.part ds asks → spBud ⟨P, a⟩ asks) →
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u

end ProofFile.Honest.K14
