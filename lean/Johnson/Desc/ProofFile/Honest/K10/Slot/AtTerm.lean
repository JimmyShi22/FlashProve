-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Slot/AtTerm.lean: the closing of a segment (K10): THE PREMISES OF `written_hand` AT THE
MAKER's RETURN, UNDER THE HEAD. Where `onlineProverFromPublicFiles` yields A at the head's files, at any filling: the lot's places at A's public
part are the 25 written ones; A's description is alike to the written one and passes the test on its places; A's book
is what `bookWhole` returns there. So the laid row at each place of `closePars A.Z` meets `Good`.

  `closePars_at_head`   under the head the lot's places are `writtenClosings`
  `return_facts`        the four facts at A
  **`closing_hand_at_return`**   at each place of `closePars A.Z` the laid row meets `Good`, with no premise but the head and
      the maker's return

  `not_a_place`          a tooth: the list tells the last closing's piece, and has no 26th link

Limits. The head is a premise (`AtFullSide.Top.headMember_named` gives it at the two named sets of public files) and so is
the maker's return (`atPure_returns_term` gives it at the term's filling, under the live test). THE SPENDER's HALF: the
owner's `fresh` at K1 and K2 is not here. `Good` is `closing_hand`'s, at A := B := False inside it.
No property of the protocol is claimed: nothing is
said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Slot.Hand
import Johnson.Desc.ProofFile.Honest.K10.Slot.Places
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.AtFull.Shape.LinkNumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Slot
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open P2Law.ProofPlan (WP)
open P5J (AtMg AtMgA TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- **Under the head the lot's places are the written ones.** -/
theorem closePars_at_head {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) : closePars Zp = writtenClosings :=
  closePars_written Zp (Johnson.AtFull.Shape.spots_at_head h) (Johnson.AtFull.Shape.entries_at_head h)
    (Johnson.AtFull.Shape.groups_at_head h)

variable {W₀ Rc Tr X₀ X : Type} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The four facts at the maker's return.** -/
theorem return_facts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    closePars A.Z = writtenClosings ∧ PlanAlike WP A.F ∧ A.F.placesOk = true ∧
      bookWhole A.F Zp.made.proof.1 Zp.made.proof.2.1 Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok A.B := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  have eF : A.F = F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  have hb := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hp : (F0T OnBytes.secondHashFunction Zp Np cF).planOk = true := h.laid.planOk
  rw [eZ, eF]
  refine ⟨closePars_at_head h.toAtMg, ProofFile.Honest.K14.planAlike_at_head h, ?_, hb⟩
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hp
  exact hp.1.1.1.1.1.2

/-- **At each place of the lot at the maker's return the laid row meets `Good`.** -/
theorem closing_hand_at_return {Xi Tr' : Type} {Wq Rq : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local Wq Rq Xi Tr') (Local Wq Rq Xi Tr') Xi) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall A.F.S₁)) (readers : Local Wq Rq Xi Tr' → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (G : ProofFile.Ground) (Q : Par) (hQ : Q ∈ closePars A.Z)
    (T : Local Wq Rq Xi Tr' → Thread A.B A.F.S₁ A.F.Cl (Local Wq Rq Xi Tr') (Local Wq Rq Xi Tr') X Xi)
    (Sd : Local Wq Rq Xi Tr' → Nat → Coins A.B → Mid (Local Wq Rq Xi Tr') X → Prop) :
    ∀ σ, ((closingRow (X := X) readers rows stAt A.Z G Q).lay T Sd A.F.first.blocksInOrder).side A.F.first.blocksInOrder fs = some σ →
      ∃ A' B', Good pre φ σ A.B ord chain firstTree A' B'
        ((closingRow (X := X) readers rows stAt A.Z G Q).lay T Sd A.F.first.blocksInOrder).On
        ((closingRow (X := X) readers rows stAt A.Z G Q).lay T Sd A.F.first.blocksInOrder).bud := by
  obtain ⟨h1, h2, h3, h4⟩ := return_facts h hA
  exact written_hand h2 h4 h3 pre φ ord chain firstTree fs readers rows stAt A.Z G Q (h1 ▸ hQ) T Sd

/-- **A tooth: the list is no letter.** The last closing stands at piece 13: at piece 11, where the first stands, it is no
member. No closing of the list stands at link 25 or beyond. -/
theorem not_a_place : writtenPar 24 11 8 1322 76 ∉ writtenClosings ∧ writtenPar 24 13 8 1322 76 ∈ writtenClosings ∧
    ∀ P ∈ writtenClosings, P.link < 25 := by
  decide +kernel

end ProofFile.Honest.K10.Slot

#print axioms ProofFile.Honest.K10.Slot.not_a_place
#print axioms ProofFile.Honest.K10.Slot.closePars_at_head
#print axioms ProofFile.Honest.K10.Slot.return_facts
#print axioms ProofFile.Honest.K10.Slot.closing_hand_at_return
