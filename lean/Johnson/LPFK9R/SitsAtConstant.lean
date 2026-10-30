-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SitsAtConstant.lean: THE SUB-PROTOCOLS THAT KIND K9's LOT LAYS AT THE SEAT
(`ProofFile.k9Ninth`, Johnson/Desc/ProofFile/Lot/K9.lean) TIED TO THE LETTERS AT WHICH K9's LAW IS STATED
AT THE CLOSED CONSTANT (`P5J.AtMg` | `AtMgA`): the carriage that was owed. Theorems.

WHY. `SitsAt c l Lk p Q` (Sits.lean) says of a link of a description's first chain what K9's law
asks
of the sub-protocols there: the batching stands at number 14 l + n + 2 of the flat list and is a
draw
with the gatherer behind it; the sub-protocol behind it is a row of moves; the one equation's stands
at + 4 and its yes is K9.oneEquation's; the shutting's at + 6. `k09_sits` proves it in scope at
every
l < 25, from k9_of and close_of, which unfold k9Ninth. ALL THAT STANDS AT
THE OPENING (`IM.Open … c …`). The list of what is left of a link's law at the closed
constant (Johnson/Desc/First/Link/Law/LinkList.lean) speaks of "the sub-protocol at number
batchAt fullLinks At.ps m of (F0T o Zp Np cF).first.blocksInOrder" and of `h.𝔇.lk m`, and asks what they are
as named fields.

What is said.
  `chain_of_open`: the opened chain is the value of the maker of the chain off the public part.
    (The same sentence stands as chain_free, Johnson/P5J/ChainFree.lean;
    its proof's steps are followed here.)
  `sits_at_constant`: **under the one head at OnBytes.secondHashFunction, at every m < 25: At.lk Zp m = some L
    and SitsAt cF m L p Q.**
  `batchAt_full`, `fullLinks_sub`: two closed facts, by the kernel: the table's number of link m's
    batching is 14 m + (the number of m's hearing kinds) + 2; the written list's sort at m is subAt
m.
  `fields_at_constant`: **THE LIST's STRUCTURAL FIELDS, AT ITS OWN LETTERS**: the sort · lk · seg ·
    atK · atK1 · drawB · movesQ · the one equation's sub-protocol at k + 2 with hb₃ (pw := p) · the
    shutting's at k + 4 with its like.

Limits. AT o := OnBytes.secondHashFunction ALONE (k09_sits stands there). In scope (the head's own fields). It
says WHAT STANDS at the numbers; nothing on what these sub-protocols decide beyond SitsAt's clauses.
NOT HERE: LinkShare | TwoBlocks (they want the sorts' Takes). Nothing on soundness.

-/
import Johnson.LPFK9R.LinkAtSeat
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Law.LinkAtLaw
import Johnson.Desc.First.Link.Law.K9KindTiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link FileDescription claimsInBy)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L (DrawMoves IsMoves Move)
open VerifiableInference.Desc.LinkJoin (SegAt batchAt)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open k9At subAt)
open P5J (AtMg AtMgA F0T fullLinks)

/-- The opened chain is the value of the maker of the chain off the public part. -/
theorem chain_of_open {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : Open o pol lay KL F Z Bs base c A B) :
    ProofFile.onlineFirstChainAt Z = .ok c := by
  have h1 : ProofFile.baseOf Z (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) = .ok Bs := O.made
  have h2 : (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).base = .ok base := O.places
  have h3 : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).road = .ok c := O.chain
  unfold ProofFile.onlineFirstChainAt ProofFile.chainOfSeat ProofFile.partsOf
  rw [h1]
  show ((ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).base.bind fun base =>
    ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) Bs).road) = _
  rw [h2]
  exact h3

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl}

/-- **K09_sits AT THE CLOSED CONSTANT's LETTERS.** -/
theorem sits_at_constant (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ m < 25, ∃ (L : Link S Cl) (p : Where) (Q : VerifiableInference.Desc.First.Close.Par),
      P5J.At.lk Zp m = some L ∧ k9At Zp m = some p ∧
        ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = some Q ∧ SitsAt cF m L p Q := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro m hm
  obtain ⟨L, p, Q, hp, hQ, hs⟩ := k09_sits h.scope h.reads O m hm
  refine ⟨L, p, Q, ?_, hp, hQ, hs⟩
  show ProofFile.linkAt Zp m = some L
  rw [ProofFile.Law.linkAt_of Zp cF (chain_of_open O) m]
  exact hs.link

/-- The table's number of link m's batching. -/
theorem batchAt_full : ∀ m < 25, batchAt fullLinks P5J.At.ps m =
    14 * m + (kindsBeforeBatching (subAt m) (m == 0)).length + 2 := by decide +kernel

/-- The written list's sort at m. -/
theorem fullLinks_sub : ∀ m < 25, fullLinks[m]? = some (subAt m) := by decide +kernel

/-- **THE LIST's STRUCTURAL FIELDS, AT ITS OWN LETTERS.** -/
theorem fields_at_constant {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    ∃ (L : Link S Cl) (p : Where) (Q : VerifiableInference.Desc.First.Close.Par),
      fullLinks[m]? = some (subAt m) ∧ h.𝔇.lk m = some L ∧ SegAt m (subAt m) L ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m]? = some L.batchB ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m + 1]? =
        some L.behindB ∧
      DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB ∧
      IsMoves atS [.quiet L.runBehind] L.behindB ∧
      (∃ b₃, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m + 1 + 1]? =
          some b₃ ∧
        ∀ ft s rs cols y, b₃.step ft s rs cols = .ok y →
          (VerifiableInference.Desc.K9.oneEquation (Cl := Cl) atS p).step ft s rs cols = .ok y) ∧
      ∃ b₅, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m + 4]? =
          some b₅ ∧
        ∀ ft s rs cols y, b₅.step ft s rs cols = .ok y →
          (VerifiableInference.Desc.K9.shut (Cl := Cl) p (Q.piece + 1)).step ft s rs cols =
            .ok y := by
  obtain ⟨L, p, Q, hlk, _, _, hs⟩ := sits_at_constant h.toAtMg m hm
  have hk : batchAt fullLinks P5J.At.ps m = 14 * m + L.hear.length + 2 := by
    rw [batchAt_full m hm, hs.hear]
  obtain ⟨b₃, _, h3, _, h3'⟩ := hs.equation
  obtain ⟨b₅, _, h5, _, h5'⟩ := hs.shut
  refine ⟨L, p, Q, fullLinks_sub m hm, hlk, segAt_of_sits hs, ?_, ?_, hs.draw, hs.behind,
    ⟨b₃, ?_, h3'⟩, b₅, ?_, h5'⟩
  · rw [hk]
    exact hs.flat
  · rw [hk]
    exact hs.flat₂
  · rw [hk]
    exact h3
  · rw [hk]
    exact h5

end LPFK9

#print axioms LPFK9.chain_of_open
#print axioms LPFK9.sits_at_constant
#print axioms LPFK9.batchAt_full
#print axioms LPFK9.fullLinks_sub
#print axioms LPFK9.fields_at_constant
