-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/AtFullStatement.lean: WHERE THE KIND's BLOCK STANDS, UNDER THE ONE HEAD OF
THE COMPOSED MEANING AT THE FULL SIZE (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean); AND, IN FRONT OF IT,
THAT THE STEP's NAME IS FOUND: STATEMENTS ALONE: two, each a definition of a proposition. NOTHING IS
PROVED IN THIS FILE, and neither is one of the library's goals: they are lemmas' statements. The
texts are the description's and the table's; no prover is named.

  `StepFoundInScope`   at public files in scope, at an opening of the description's return
                       (`IM.Open`, Johnson/IMR/SeatOpen.lean) at the library's constant for the
                       format's second hash function, WHERE THE DESCRIPTION PASSES ITS TESTS ON THE PLAN:
                       `verify-on-bytes`'s step under the name that the kind's lot looks up is
                       found: the one premise that `HeadMergeInScope` (InScopeStatement.lean of this
                       folder) takes beside the opening
  `HeadMergeAtFull`    under the one head, at that earlier hash, WITH NO OTHER PREMISE: there are
                       what the maker's own `ProofFile.baseOf` returns at the head's public part, a link
                       and a name such that, with K the kind's block AT THE LOT's NUMBERS as it
                       stands alone at the seat of that name at the kind's address:
                         THE DATA OF THE COMPOSED MEANING UNDER THAT HEAD have that link at segment
                           24; 24 is of the head's sort in their list of segments; their layout of
                           the weights is the lot's;
                         the link's hearing block number 8 is K;
                         the member number 346 of the flat list of the head's own chain is K;
                         the lot's number of the link is 24

Why. `HeadMergeInScope` leaves open that the public part of some data of the composed meaning is the
opening's, and that the step's name is found. The head holds an opening at its own letters, and that
the description passes its tests on the plan.

Limits. The head itself is a premise. At that one earlier hash. Of the data's other numbers (the
columns' bits; that the rows fit) nothing. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.InScopeStatement
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)

/-- The statement that the step's name is found. The letters: as in `HeadMergeInScope`. Not proved
here; a lemma's statement, none of the library's goals. -/
def StepFoundInScope : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat),
    VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B → F.planOk = true →
    (K11.sentAt? Z "H.8.call").isSome = true

/-- The statement under the one head. Z, D, r, Zp, Np, cF, x: the head's letters: Zp is the public
part, cF the first chain. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeAtFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x),
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S Cl) (name : String),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      h.𝔇.lk 24 = some Lk ∧ h.𝔇.links[24]? = some .head ∧
      h.𝔇.d1.lay = (K11.parOf Zp Bs.G₀).lay ∧
      Lk.hear[8]? =
        some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Zp Bs.G₀)) name IM.k11Place) ∧
      cF.blocksInOrder[346]? =
        some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Zp Bs.G₀)) name IM.k11Place) ∧
      (K11.parOf Zp Bs.G₀).link = 24

end Johnson.Desc.First.ForkMerge.Exchange
