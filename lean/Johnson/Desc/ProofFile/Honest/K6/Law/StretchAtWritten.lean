-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/StretchAtWritten.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
UNDER THE HYPOTHESIS h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): THE LIST OF SENDINGS AT WHICH THE
MAKER OF THE BOOK OF COINS SEEKS LINK 24's MASK ROW IS THE LIBRARY's WRITTEN ONE
(`Johnson.G.proofSendsFull`, Johnson/G/SendsWritten.lean). No definition; three theorems.

  `k6_sends_fifth`          under h: of the seven lists that `Johnson.G.sendsOf` returns at the
                            head's files the fifth is the written first chain's
  `k6_book_of_atPure_sends` GENERAL: `k6_book_of_atPure` (Honest/K6/Law/StretchAtBook.lean), with
                            where the three lists come from
  `k6_stretch_at_written`   under h and hA: `k6_stretch_at_atPure` (the same file) with the list of
                            sendings NAMED

By, the library's: `sends_tie` (Johnson/LPFE1R/RadiiAt.lean) and `made_parts`
(Johnson/Desc/First/Link/Law/EndsOfMade.lean): two returns of one call of `sendsFrom`, so the fifth
is the public part's own first proof chain; `AtMg.pins` (Johnson/P5T/FenceAtMg.lean) and `IM.pins`
(Johnson/IMR/SendsPinned.lean): that chain is the written one.

What it is not.
  * **WHICH ADDRESS row.owner IS, AND WHICH NUMBER row.base.e IS, IS STILL NOT SAID.** One letter of
    `ownerOf`'s equation is turned into a written list. Its other two (the first chain's flat list;
    the second chain's rounds) are the head's own terms, no written lists.
  * Of the seven lists the fifth alone is spoken of.
  * hA IS A PREMISE: that the frame's maker returns at any files is not shown here.
  * h: the full size and the format's second hash function alone.
  * Public data alone: nothing on a coin's value or on a run.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.StretchAtBook
import Johnson.IMR.SendsPinned
import Johnson.LPFE1R.RadiiAt
import Johnson.Desc.First.Link.Law.EndsOfMade
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Kinds (Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf takesOf)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- CONDITIONAL: h; hs. **Of the seven lists that the library's `sendsOf` returns at the head's
files the fifth is the written one.** -/
theorem k6_sends_fifth (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {k0 k1 k2 e0 p0 p1 p2 : Johnson.G.ChainSends}
    (hs : Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e0, p0, p1, p2]) :
    p0 = Johnson.G.proofSendsFull.1 := by
  have t := VerifiableInference.Desc.LinkJoin.sends_tie h.laid.pub hs
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨⟨a0, a1, a2, a3, a5, a6, hm⟩, -⟩ := VerifiableInference.Desc.LinkJoin.made_parts hZ
  rw [hm] at t
  have e := Except.ok.inj t
  simp only [List.cons.injEq] at e
  obtain ⟨-, -, -, -, e5, -⟩ := e
  rw [← e5, (IM.pins h.toAtMg.pins.1).2.2.2.2]

/-- GENERAL. Where the frame's maker returns A: the library's `sendsOf` returns seven lists at the
files, and A.B is what the whole book's maker returns at A.F, the last three of them and the merges
by name. -/
theorem k6_book_of_atPure_sends {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ k0 k1 k2 e0 p0 p1 p2, Johnson.G.sendsOf pol lay KL = .ok [k0, k1, k2, e0, p0, p1, p2] ∧
      bookWhole A.F p0 p1 p2 (mergesByName A.F.first.blocksInOrder) = .ok A.B := by
  unfold onlineProverFromPublicFiles at hA
  obtain ⟨Z', _, hA⟩ := bind_ok hA
  obtain ⟨G, _, hA⟩ := bind_ok hA
  obtain ⟨F, _, hA⟩ := bind_ok hA
  obtain ⟨cs, hcs, hA⟩ := bind_ok hA
  split at hA
  · obtain ⟨B, hB, hA⟩ := bind_ok hA
    dsimp only at hA
    split at hA
    · cases hA
    · split at hA
      · cases hA
      · cases hA
        exact ⟨_, _, _, _, _, _, _, hcs, hB⟩
  · cases hA

/-- CONDITIONAL: h; hA. **THE TEXT OF THE FIELD stretch AT THE BOOK OF THE PROVER THAT THE FRAME's
MAKER RETURNS, WITH THE LIST OF SENDINGS NAMED: THE WRITTEN ONE.** -/
theorem k6_stretch_at_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) :
    ∃ row, ownerOf maskRowRun cF.blocksInOrder Johnson.G.proofSendsFull.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        s!"link {24}, moment 0" isMaskRowMsg = some row ∧
      oneStretch (rowEntries A.B IM.k6Place (headRow (X := X) wit
        (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).length 0) =
        some (row.owner, row.base.e + OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs,
          takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) := by
  obtain ⟨k0, k1, k2, e0, p0, p1, p2, hs, hB⟩ := k6_book_of_atPure_sends hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  rw [eF] at hB
  obtain ⟨row, h1, h2⟩ := k6_stretch_at_book (X := X) h hB wit
  rw [k6_sends_fifth h hs] at h1
  exact ⟨row, h1, h2⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_sends_fifth
#print axioms ProofFile.Honest.K6.k6_book_of_atPure_sends
#print axioms ProofFile.Honest.K6.k6_stretch_at_written
