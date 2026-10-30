-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingRowsStated.lean: kind K14: A FORM AND A STATEMENT, EACH AS
THE DEFINITION OF A PROPOSITION, WITH NO PROOF IN THIS FILE: what the frame's rule for rows
(file_owed_rows, Honest/Thread/Rows.lean) asks of the two sendings' rows (sendingRows,
Honest/K14/ExactRows.lean), AT THE OWN MEMBERS OF THE PROOF FILE's IOP AS WRITTEN IN LEAN (below:
the description): the side, the sub-protocol and the shared rounds' parameters are not left free.
LEFT FREE: the book, the order of places, the falls and the two readers of the input (weights,
rand). THIS FILE STATES NO GOAL OF THE RELEASE: the two count as none.

  RowsServe       at a list of sub-protocols, public data A, a book and an order of places: for each
                  of the two rows: the list has a member at the row's place; and every side that
                  Side.seated (Honest/Side.lean) takes off the list there, beside the row, has the
                  three fields of Good that the rule reads: fits · exact, at the shared rounds'
                  face, chain 1, first tree 0, the row's own sentence at entry and bound · fresh,
                  where the two owners' tests on the book accept
  SendingRowsAtHead   RowsServe under the library's head, at the shared rounds' own flat list
                  carried to any type of claims, at the parameters that the description's maker lays
                  there, with "LIN point" as round number 0

How it follows (Honest/K14/SendingRowsLaw.lean). The member, the place, the declared rounds and
SendDeclared: seated_declares_head (Honest/K14/SendingsSeated.lean). The shapes: sendings_at_head
(Honest/K14/SendingsAtHead.lean). fits: from the place, two declared rounds and two lists of oracle
messages. exact: exactAtU and exactAtOmega (Honest/K14/ExactSend.lean). fresh: the laws at the two
owners' tests (sp_owner_law', Honest/K14/FreshOwnerLaw.lean; maskOwnerLaw',
Honest/K14/MaskSend.lean).

WITH BOTH. What a part shows is not all that a run shows of its messages and coins: the proximity
tests behind the sendings, and of o_omega each request's own test, are handed these messages' coins;
nothing is said here of what they show · the challenges and the positions are fixed before the coins
are sampled · that the row's sentence at entry holds where a run stands, and that a run's positions
are within the row's bound, is to be had beside these statements, at the same On and bud (the first,
out of the frame's sentence on where a run stands, which nothing shows to hold along a run:
Honest/K14/OnSending.lean; of the second, the count at the positions that the frame lays at one
request's challenges, not at a run's: Honest/K14/BudRows.lean) · that any book passes the two tests
is not claimed · one request · no property is claimed.
What is not claimed. In this file: that the statement holds. That a filling of the frame lays its
sides for these two rows off that list: the list is the shared rounds' own flat list carried to a
type of claims; that it is a description's field shared, blocksInOrder, is one equation more
(rowsServe_at_shared, Honest/K14/RowsAtShared.lean). Anything on the key's own answers or the stored
columns. Anything on what is or is not hidden.
-/
import Johnson.Desc.ProofFile.Honest.K14.ExactRows
import Johnson.Desc.ProofFile.Honest.K14.MaskOwner
import Johnson.Desc.ProofFile.Honest.K14.FreshOwner
import Johnson.Desc.ProofFile.Honest.K14.SendingsSeated
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (St chainOf)
open ProofFile.Honest.Small (ExactMember FreshMember)

/-- **What the rule for rows reads of Good, at each of the two sendings' rows, at every side that is
taken off the list xs at the row's place.** The list has a member at the place; and at each such
side: fits · exact, at the shared rounds' face, chain 1, first tree 0, the row's own sentence at
entry and bound · fresh ONLY WHERE BOTH OWNERS' TESTS ON THE BOOK ACCEPT. A definition: the form of
a conclusion. WHAT A PART SHOWS IS NOT ALL THAT A RUN SHOWS OF ITS MESSAGES: the proximity tests
behind it are handed these messages' coins; nothing is said here of what they show. -/
def RowsServe {Cl X W₀ Rc Ky : Type} (xs : List (Block St Cl)) (A : SendPub)
    (weights : W₀ → Weights) (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts)
    (ord : List Place) : Prop :=
  ∀ r ∈ (sendingRows A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Ky)),
    xs.any (fun b => b.place == r.place) = true ∧
    ∀ σ : Side St Cl Empty (Common W₀ Rc Ky) X Ky,
      Side.seated xs r.place r.row fs = some σ →
      σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember .shared σ 1 0 r.On r.bud u) ∧
      ((maskOwner A).ok Bk ord ⟨sendPlace 2, 0⟩ = true →
        (spOwner A).ok Bk ord ⟨sendPlace 5, 0⟩ = true →
        ∀ u ∈ σ.members, FreshMember .shared σ Bk ord r.bud u)

/-- **The two rows serve at the description's own members** (RowsServe: fresh only where both
owners' tests on the book accept), under the library's head. A STATEMENT, NOT A THEOREM IN THIS
FILE; its proof: sendingRowsAtHead, Honest/K14/SendingRowsLaw.lean. No property is claimed. -/
def SendingRowsAtHead : Prop :=
  ∀ {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (_h : P5J.AtMgA o Z D r Zp Np cF x₀) (Cl X W₀ Rc Ky : Type) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place),
    RowsServe (X := X) (Ky := Ky)
      ((chainOf Zp.p.chains (qAt Zp Np) (tests Np) last).retype (Cl' := Cl)).blocksInOrder
      ⟨qAt Zp Np, 0⟩ weights rand fs Bk ord

end ProofFile.Honest.K14
