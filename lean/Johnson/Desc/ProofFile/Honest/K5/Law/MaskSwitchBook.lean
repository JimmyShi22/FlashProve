-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/MaskSwitchBook.lean: CONDITIONAL: THE THREE TOPS OF
MaskSwitch.lean (in this folder) WITH THEIR TWO PREMISES AT EVERY RUN EXCHANGED FOR TESTS WITH CODE
ON PUBLIC DATA: AN EXCHANGE, NOT A PAYMENT: hB is derived from hT by `rowIsStretch_of`, hL from hR
by `lends5_iff`; hT AND hR STAY PREMISES. The agreement of the lot of K5's slots with the code
switch's whole-message lot then stands under public premises alone: a test on the book and numbers.
Of the coverings' premises two stay that are no tests: hnum and hS. The tests are run here at no
book. No definition; three theorems.

What it is for. MaskSwitch.lean takes `RowIsStretch` and `Lends5` as they are typed: sentences at
every run. Each follows from, or is, a test that takes no run: hT's reads the book alone, with K5's
place and the row's number of parts; hR's reads the book and K5's row at its place. Here these tests
stand in the statements, so that what is asked of a book can be run.

Main names:
  `agree2_mask_switch_book`: `agree2_mask_switch` with hT in the stead of hB.
  `covers_mask_switch_book`: `covers_mask_switch` likewise.
  `covers_mask_switch_at_book`: `covers_mask_switch_at` with hT in the stead of hB and hR in the
    stead of hL.

THE PREMISES, ALL OF THEM.
  hT: ON THE BOOK: A TEST WITH CODE: `oneStretch (rowEntries Bk Z5.place (H2K5.Honest.shapes
    Z5.P.x).length 0)` (Johnson/Desc/ProofFile/Honest/BookStretch.lean) answers the triple: the
    switch's part's address; the number `K2.maskBase … n` + ν₅; cnt: the book's spending entries of
    K5's row are one stretch of that owner's run, from that number on, cnt long: AMONG THE OWNER's
    ENTRIES OF THE EXTENSION FIELD: of an entry's start and count the test reads that field's half
    alone. RUN HERE AT NO BOOK.
  hR (`covers_mask_switch_at_book`): ON THE BOOK AND K5's ROW: ONE Bool: `lendsRow Bk 0 Z5.place
    (k5Row Z5)` (Johnson/Desc/ProofFile/Honest/Small/LendsRow.lean) says yes. RUN HERE AT NO BOOK.
  hn, hl, h1, hN: PUBLIC: as in MaskSwitch.lean: n is a message of the switch's sending, not the
    last; it has one mask row; K5's slots lie within that row.
  hnum, hS (the two coverings): as in MaskSwitch.lean: NAMED, NOT PAID: the two lots bear one
    number; at every run and input of which `Covers` speaks, wherever K5's text answers, the
    switch's does.
  h: the library's hypothesis on the public input (`P5J.AtMgA`): a letter of `maskLot`, as in
    MaskSwitch.lean, with the fence told there.
  D₁, rd, closing, p, n, cnt, fx, x₁, kM, Z5, ν₅ ARE LETTERS, and cells in
    `covers_mask_switch_at_book`, of which nothing is asked. NOTHING TIES THE SWITCH's PLACE p AND
    ITS MESSAGE n TO K5's SEGMENT (x₁, Z5) BUT hT AND hnum.

How. One line each: `rowIsStretch_of` (Johnson/Desc/ProofFile/Honest/BookStretch.lean): the test's
answer gives `RowIsStretch` at every chain; `lends5_iff` (LendsRow5.lean in this folder): `Lends5`
is that Bool, at every reader of the witness.

Limits. CONDITIONAL. THEY MAY HOLD EMPTILY, in all the ways told in MaskSwitch.lean; and where the
test answers another triple, or none, hT fails and nothing is said: by its text `oneStretch` answers
none at a row that has no spending entry. That hT or hR holds at any book is not said. All Limits of
MaskSwitch.lean stand, but that hB and hL are derived from hT and hR: THE DEBT IS MOVED, to two
tests that can be run. BookStretch.lean's own Limits bear on hT: the extension field's entries
alone; a row that spends of two messages fails the test; that the first number is the one that the
plan gives (`startOf`, Johnson/Desc/ProofFile/Honest/BookStart.lean) is not said there: hT asks it
to be `K2.maskBase … n` + ν₅, and that a book's maker lays it so is said nowhere here. The file
stands over BookStretch.lean, LendsRow5.lean and MaskSwitch.lean, and what lies beneath them: none
of the three lies in a seal. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean,
and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the
earlier hash `OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskSwitch
import Johnson.Desc.ProofFile.Honest.BookStretch
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsRow5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (sigListCalls)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers)
open P5J (AtMgA TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **`agree2_mask_switch` WITH ITS PREMISE AT EVERY RUN EXCHANGED FOR A TEST ON THE BOOK.**
CONDITIONAL: hT: the test `oneStretch` on the book's spending entries of K5's row says: one stretch,
of the switch's part's own run, from the number of message n's first mask entry + ν₅ on, cnt long;
hn, hl, h1, hN: as there: public. -/
theorem agree2_mask_switch_book {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {ν₅ : ℕ}
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) {n cnt : ℕ} (num fx : ℕ)
    (hn : n < (K2.switchSent p.sizes p.others).size)
    (hl : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (h1 : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hT : oneStretch (rowEntries Bk Z5.place (H2K5.Honest.shapes Z5.P.x).length 0) =
      some (⟨p.place, 0⟩, K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅, cnt))
    (hN : ∀ j, j < cnt →
      ν₅ + j < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n) :
    Agree2 (maskLot (Bk := Bk) (W₀ := W₀) (Rc := Rc) (Tr := Tr) h x₁ kM hk Z5 ν₅)
      ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩ :=
  agree2_mask_switch h D₁ rd closing p num fx hn hl h1 (rowIsStretch_of hT) hN

/-- **`covers_mask_switch` LIKEWISE.** CONDITIONAL: hT in the stead of hB; the rest as there. -/
theorem covers_mask_switch_book {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {ν₅ : ℕ}
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) {n cnt num : ℕ} (fx : ℕ) (hnum : num = maskNo5 h x₁ kM hk)
    (hn : n < (K2.switchSent p.sizes p.others).size)
    (hl : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (h1 : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hT : oneStretch (rowEntries Bk Z5.place (H2K5.Honest.shapes Z5.P.x).length 0) =
      some (⟨p.place, 0⟩, K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅, cnt))
    (hN : ∀ j, j < cnt →
      ν₅ + j < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      (maskTxt Bk Z5 ν₅ k w (hd.take 0) mask row place).isSome = true →
      (K2.switchMsgTxt 0 D₁ rd closing p n k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩
      (maskLot (Bk := Bk) h x₁ kM hk Z5 ν₅) :=
  covers_mask_switch h D₁ rd closing p fx hnum hn hl h1 (rowIsStretch_of hT) hN hS

/-- **`covers_mask_switch_at` WITH BOTH PREMISES AT EVERY RUN EXCHANGED FOR TESTS ON PUBLIC DATA.**
CONDITIONAL: hT in the stead of hB; hR in the stead of hL: the Bool `lendsRow` of the book and K5's
row says yes; cells: a letter, of which nothing is asked; the rest as there. -/
theorem covers_mask_switch_at_book {x₁ : VerifiableInference.Desc.First.Look.Place} {kM : ℕ}
    {hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length} {Z5 : Seat5} {ν₅ : ℕ}
    (D₁ : RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) {n cnt num : ℕ} (fx : ℕ) (hnum : num = maskNo5 h x₁ kM hk)
    (hn : n < (K2.switchSent p.sizes p.others).size)
    (hl : n ≠ (K2.switchSent p.sizes p.others).size - 1)
    (h1 : ((K2.switchSent p.sizes p.others).getD n default).shape.maskRows = 1)
    (hT : oneStretch (rowEntries Bk Z5.place (H2K5.Honest.shapes Z5.P.x).length 0) =
      some (⟨p.place, 0⟩, K2.maskBase p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) n + ν₅, cnt))
    (hN : ∀ j, j < cnt →
      ν₅ + j < K2.maskLength p.sizes.codes (K2.switchSent p.sizes p.others) n)
    (cells : Tr → Cells) (hR : lendsRow Bk 0 Z5.place (k5Row Z5) = true)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      maskAnswers Z5 ν₅ mask row place = true →
      (K2.switchMsgTxt 0 D₁ rd closing p n k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N ⟨num, fx, K2.switchMsgTxt 0 D₁ rd closing p n⟩
      (maskLot (Bk := Bk) h x₁ kM hk Z5 ν₅) :=
  covers_mask_switch_at h D₁ rd closing p fx hnum hn hl h1 (rowIsStretch_of hT) hN
    ((lends5_iff (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := Unit) Bk cells Z5).2 hR) hS

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.agree2_mask_switch_book
#print axioms ProofFile.Honest.K5.covers_mask_switch_book
#print axioms ProofFile.Honest.K5.covers_mask_switch_at_book
