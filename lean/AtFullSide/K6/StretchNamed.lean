-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K6/StretchNamed.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): UNDER THE HYPOTHESIS h
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) AND "THE FRAME's MAKER RETURNS": WHAT K6's ROW OF PARTS
SPENDS IS ONE STRETCH OF COINS, WITH ITS OWNER AND ITS START NAMED: THE TEXT OF THE FIELD stretch OF
`K6HeadBelow` (Johnson/Desc/ProofFile/Honest/K6/Law/ScriptBelowFree.lean) AT
o := ⟨⟨1, some 24, 2, .K2⟩, 0⟩, base := 439, cnt := takesOf …; AND THE FIELD below AT EVERY free
FROM 2168 ON. No definition; four theorems.

  `k6_row_named`         under h: what the book's maker's `ownerOf` finds as the owner of link 24's
                         mask row, at the head's own description and the written sendings, is a
                         written value
  `k6_stretch_named`     under h and hA: the field stretch at A.B, owner and start named
  `k6_stretch_numerals`  the same in numerals: eight parts; from 439 + 1995 on; 173
  `k6_below_of`          under h: 2168 ≤ free gives the field below

By. `k6_stretch_at_written` (Honest/K6/Law/StretchAtWritten.lean). OF OTHER AUTHORS' GROUPS:
`rawRows_written` (AtFullSide/K14/RawFactsWritten.lean): the written value, at the library's written
description `WP`, BY ONE EVALUATION IN LEAN's KERNEL OVER ALL 25 LINKS; `planAlike_at_head`
(Honest/K14/WrittenAtHead.lean): under h the head's own description is alike to `WP`. Ours:
`ownerOf_alike` (Honest/BookAlike.lean). The library's `alike₂_rounds`
(Johnson/AtFull/ProofPlan/PlanAlike.lean). `k6_elems_at_head`, `k6_takes_at_head`,
`k6_window_at_head` (Honest/K6/Law/WindowNumbers.lean).

What it is not.
  * hA IS A PREMISE: that the frame's maker returns at any files is not shown here.
  * THE NUMERALS ARE ANOTHER GROUP's CLOSED FACT. It finds the sending BY ITS LABEL; the written
    sendings' labels rest on one print of Lean's evaluator and on one test at every build
    (Johnson/G/SendsWritten.lean's own limit).
  * That the address is the code switch's and 439 the number at which the switch's authors lay that
    message's mask entries: AtFullSide/K6/StretchAtSwitch.lean.
  * THE WRITTEN VALUE's FOURTH FIELD, 8191, IS THE MASK ROW's OWN NUMBER OF FREE ENTRIES, NOT THE
    RECORD's LETTER free: that letter stands in four fields of the record (below, reader, sender,
    inside), and who pays reader may ask more of it than below does.
  * That this stretch lies apart from what another part spends: Honest/K6/Law/OnceAtBook.lean.
  * h: the full size and the format's second hash function alone.
  * Public data alone: a book is a table of entries: nothing on a coin's value or on a run.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import AtFullSide.K14.RawFactsWritten
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.BookAlike
import Johnson.Desc.ProofFile.Honest.K6.Law.StretchAtWritten

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

/-- CONDITIONAL: the hypothesis h. **THE OWNER OF LINK 24's MASK ROW, AS THE BOOK's MAKER FINDS IT
AT THE HEAD's OWN DESCRIPTION AND THE WRITTEN SENDINGS, IS A WRITTEN VALUE**: its name; the part
that sends it; where its entries begin among that part's coins; its free entries. -/
theorem k6_row_named (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ownerOf maskRowRun cF.blocksInOrder Johnson.G.proofSendsFull.1
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        s!"link {24}, moment 0" isMaskRowMsg =
      some ⟨maskRowRun, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 8191⟩ := by
  have A := ProofFile.Honest.K14.planAlike_at_head h
  show ownerOf maskRowRun (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder Johnson.G.proofSendsFull.1
      ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
      s!"link {24}, moment 0" isMaskRowMsg =
    some ⟨maskRowRun, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 8191⟩
  rw [← ownerOf_alike A.first, ← VerifiableInference.Desc.alike₂_rounds _ _ A.second]
  exact AtFullSide.K14.rawRows_written
    (24, ⟨maskRowRun, ⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨23217, 439⟩, 8191⟩) (by decide)

/-- CONDITIONAL: h; hA. **THE TEXT OF THE FIELD stretch AT THE BOOK OF THE PROVER THAT THE FRAME's
MAKER RETURNS: OWNER AND START NAMED.** -/
theorem k6_stretch_named (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) :
    oneStretch (rowEntries A.B IM.k6Place (headRow (X := X) wit
      (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).length 0) =
      some (⟨⟨1, some 24, 2, .K2⟩, 0⟩, 439 + OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs,
        takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) := by
  obtain ⟨row, h1, h2⟩ := k6_stretch_at_written (X := X) h hA wit
  rw [k6_row_named h] at h1
  have e := Option.some.inj h1
  subst e
  exact h2

/-- CONDITIONAL: h; hA. **THE SAME IN NUMERALS.** wit is read by the proof alone, for the row's
length. -/
theorem k6_stretch_numerals (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) :
    oneStretch (rowEntries A.B IM.k6Place 8 0) =
      some (⟨⟨1, some 24, 2, .K2⟩, 0⟩, 439 + 1995, 173) := by
  have s := k6_stretch_named (X := X) h hA wit
  rw [k6_elems_at_head h, k6_takes_at_head h] at s
  exact s

/-- CONDITIONAL: h; hf. **THE TEXT OF THE FIELD below, AT EVERY free FROM 2168 ON.** -/
theorem k6_below_of (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {free : Nat}
    (hf : 2168 ≤ free) :
    OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs +
      takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) ≤ free := by
  rw [k6_window_at_head h]
  exact hf

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_row_named
#print axioms ProofFile.Honest.K6.k6_stretch_named
#print axioms ProofFile.Honest.K6.k6_stretch_numerals
#print axioms ProofFile.Honest.K6.k6_below_of
