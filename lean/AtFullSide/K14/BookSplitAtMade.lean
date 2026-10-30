-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
AtFullSide/K14/BookSplitAtMade.lean: kind K14: the book of coins of the honest prover that onlineProverFromPublicFiles
makes, at the one coin that the part at "SPLIT" spends. Two statements; no definition; no evaluation
of its own: a join of laws that stand in the library.

The part at "SPLIT" (part 0 at piece 8 of the shared chain) sends one scalar plus one mask entry.
The mask entry is a coin of another part, the sender of "send o_omega" (part 0 at piece 5), and the
book of coins (ProverCoinCounts, Honest/Frame.lean) is what lends it. The kind's statements at "SPLIT" ask one
thing of the book (the field "book" of K14Asks, Honest/K14/Asks.lean): every entry by which the part
at "SPLIT" spends coins names that sender as the owner, and starts at the first coin of the split's
mask message. This file states it of the book that onlineProverFromPublicFiles (Honest/AtPure.lean) makes, at the full
size, at every filling.

  book_at_made            **the field "book" of K14Asks at the made prover's book**, to the letter
  bookSplitFits_at_made   the public test bookSplitFits (Honest/K14/Thread2Full.lean) accepts that
                          book: it asks besides that there is such an entry

From what. makers_book_one, makers_ahead_at_atPure (AtFullSide/K14/MakersBookOne.lean): whatever
onlineProverFromPublicFiles returns has the one book that the book's maker returns, and its entries are the library's
list rawAheadW. he_at_laid (AtFullSide/K12/CutsAtLaid.lean): the sentence at that book, with the
number 42853. sendNumbers_head, sendNumbers_of (Honest/K12/SendNumbersAtHead.lean): the split's mask
message begins at coin number 42853 of its sender's coins. spent_split_written (CutsAtLaid.lean): in
rawAheadW the part at "SPLIT" spends exactly one entry. That the sentence can fail: he_bite
(CutsAtLaid.lean): at every other number it is false. Kin: he_head (AtFullSide/K12/CutsAtHead.lean)
has the sentence at the book's maker's return, with the place written as the eighth sub-protocol's.

"At the full size" is the premise h : P5J.AtMgA (Johnson/P5J/MgAtAll.lean) at the hash
OnBytes.secondHashFunction. "Made" is the premise hA: onlineProverFromPublicFiles returns A at that public part's three files. The
filling P is free, so the statements hold at whichever filling a caller lays.

Limits.
  * THE PREMISE h IS A HYPOTHESIS. It gathers conditions on the public files at the full size. This
    file does not show them to be met, and the verifier does not ask them. By that file's head a
    member is proved at two written sets of public files (AtFullSide/Top/: headMember_zFull,
    headMember_zGap), and at no others.
  * That onlineProverFromPublicFiles returns is a premise and is not proved here. Where it does not return, the
    statements say nothing.
  * The number is that of one written description. Nothing is said at another size.
  * Nothing is said of an entry's name or count, nor of entries that carry.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.K14.MakersBookOne
import AtFullSide.K12.CutsAtLaid
import Johnson.Desc.ProofFile.Honest.K12.SendNumbersAtHead
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)
open P5J (TS)
open AtFullSide.K12 (he_at_laid spent_split_written)
open ProofFile.Honest.K12.Light (sendNumbers_of sendNumbers_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The field "book" of K14Asks at the made prover's book**, to the letter: every entry by which
the part at "SPLIT" spends coins names the sender of "send o_omega" as the owner, and starts at the
first coin of the split's mask message. -/
theorem book_at_made (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩ := by
  obtain ⟨B, -, hB, -, -, hall⟩ := makers_book_one h
  rw [(hall _ _ _ _ _ P A hA).1, (sendNumbers_of _ (sendNumbers_head h.toAtMg)).2.2.1]
  exact he_at_laid h.scope h.laid hB

/-- **The public test on the book accepts the made prover's book**: there is an entry by which the
part at "SPLIT" spends, and every such entry has the owner and the start that the kind's statement
at "SPLIT" asks for. -/
theorem bookSplitFits_at_made (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookSplitFits A.B (qAt Zp Np) = true := by
  have hb := book_at_made h hA
  unfold bookSplitFits
  rw [Bool.and_eq_true]
  constructor
  · rw [(makers_ahead_at_atPure h hA).1]
    have hne : ((rawAheadW.filter fun e => e.spender == ⟨place 8, 0⟩).filter (·.once)) ≠ [] := by
      intro h0
      have t := spent_split_written
      rw [h0] at t
      cases t
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨he1, ho⟩ := List.mem_filter.1 he
    obtain ⟨he2, hs⟩ := List.mem_filter.1 he1
    exact List.any_eq_true.2 ⟨e, he2, Bool.and_eq_true_iff.2 ⟨hs, ho⟩⟩
  · refine List.all_eq_true.2 fun e he => ?_
    by_cases c : (e.spender == ⟨place 8, 0⟩ && e.once) = true
    · obtain ⟨c1, c2⟩ := Bool.and_eq_true_iff.1 c
      obtain ⟨o1, o2⟩ := hb e he (beq_iff_eq.1 c1) c2
      rw [o1, o2, beq_self_eq_true, beq_self_eq_true]
      simp
    · rw [Bool.not_eq_true] at c
      rw [c]
      rfl

end AtFullSide.K14

#print axioms AtFullSide.K14.book_at_made
#print axioms AtFullSide.K14.bookSplitFits_at_made
