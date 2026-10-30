-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/WayBackFill.lean: THE FILLING LAYS AN ARRAY's ELEMENT AT THE
PLACE THAT THE LAYOUT's RULE GIVES: CONDITIONAL on the programs' own test on a layout
(`reqLayoutOk`, OnBytes/Iop/ReqRows.lean) and on the message's having a sample, which their test on
a request's shape gives: the filling of the main rows (`laidData`,
Johnson/Desc/ProofFile/Honest/LaidData.lean), read through its one call (`RowData.at_`, RowData.lean
beside it) or through the call that asks first (`RowData.ask`) at the row and place at which the
layout lays element (i, c) of an array, answers the arrays' value of that array's name at (i, c).
Lemmas over WayBack.lean in this folder. The values are letters: nothing is said of what they are.

Main names:
  `blockBack_of_laidIn`: one block: the way back undoes the rule, in the words of
    Johnson/Desc/LaidAt.lean (its option-valued `laidIn`).
  `sizes_of_layoutOk`: under the programs' test on a layout every array has at least one row and
    one column: so `laidBack_covers` (WayBack.lean) speaks of an element wherever the layout has an
    array.
  `msgFits_of_layoutOk`: **the programs' test gives the frame's test on one message (`msgFits`)
    where the message has a sample.**
  `msgFits_of_tests`: the same with that premise paid by the programs' test on a request's shape
    (`reqShapeOk`, OnBytes/Iop/Req.lean).
  `laidData_at`: **the filling at the rule's place**, read through `RowData.at_`.
  `laidData_ask`: **the same through the call that asks first** (`RowData.ask`), under the programs'
    two public tests.
  `laidBack_of_seat_named`: `laidBack_of_seat` (WayBack.lean) with one clause more: the array's name
    is the name under which the segment's list has it.

How. `Meaning.laidIn_eq` (Johnson/Goal/Meaning/ReadingsOne.lean): the two writings of the rule at a
block. `Own.reqMessageLaid_eq` (Johnson/Desc/Own/ReqAgree.lean): the plan's own test on one
message's arrays is the programs'; `Meaning.message_of_layout`
(Johnson/Goal/Meaning/LaidInside.lean): the programs' test on a layout holds it at every message
that an array names.

Limits. That a message which holds an array has a sample is a premise (hs) of `msgFits_of_layoutOk`
and `laidData_at`: no clause of `reqLayoutOk` says it; `msgFits_of_tests` and `laidData_ask` pay it
by `Meaning.answers_of_shape` (Johnson/Goal/Meaning/LaidInside.lean). Both public tests are met
wherever the public part is made: `Meaning.K2.pub_layoutOk` (Johnson/IMR/LayoutOkPub.lean);
`ProofFile.Law.startOk_shape` (Johnson/Desc/K1/Law/FirstMakeFacts.lean) with `ProofFile.Law.startP_ok` and
`Meaning.K2.pub_start`: not called here. `RowData.at_` asks neither whether enough challenges have
been heard nor the filling's own test: `laidData_at` says nothing of these. The seat of an address,
the number of challenges heard and the values are letters: that a frame's own seat and values meet
hA, hz, hi, hc, hh, hr is not shown here. hi and hc are at the size that the values say, not at the
layout's. One direction, as in WayBack.lean.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.WayBack
import Johnson.Desc.Own.ReqAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc.First.Look (Sent Seat seatCalls)

/-- **The same in the words of Johnson/Desc/LaidAt.lean**: its `laidIn` answers just where the block
holds the element. Conditional: h: where the block lays the element; hs. -/
theorem blockBack_of_laidIn {b : LaidBlock} {i c : ℕ} {p : ℕ × ℕ}
    (h : VerifiableInference.Desc.laidIn b i c = some p)
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) : blockBack b p.1 p.2 = some (i, c) := by
  rw [Meaning.laidIn_eq] at h
  split at h
  · rename_i hh
    obtain rfl := Option.some.inj h
    exact blockBack_laidIn hh hs
  · cases h

section
variable {codes : Codes} {shape : ReqShape} {layout : ReqLayout}

/-- **Under the programs' test on a layout every array has an element**: at least one row and one
column. Conditional: ok; hl, hA: the array is one of the segment's. -/
theorem sizes_of_layoutOk (ok : reqLayoutOk codes shape layout = true) {l : ℕ}
    {as : List ReqArray} (hl : layout.link[l]? = some as) {a : ReqArray} (hA : a ∈ as) :
    0 < a.sizeI ∧ 0 < a.sizeC := by
  unfold reqLayoutOk at ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, zipT_eq, decide_eq_true_eq] at ok
  obtain ⟨hlen, hall⟩ := ok
  obtain ⟨hl1, hl2⟩ := List.getElem?_eq_some_iff.1 hl
  have hmem : (shape.link[l]'(hlen ▸ hl1), as) ∈ shape.link.zip layout.link := by
    have hz : l < (shape.link.zip layout.link).length := by
      rw [List.length_zip]
      omega
    have e : (shape.link.zip layout.link)[l] = (shape.link[l]'(hlen ▸ hl1), as) := by
      rw [List.getElem_zip, hl2]
    exact e ▸ List.getElem_mem hz
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := hall _ hmem
  have k := h1 a hA
  unfold reqArrayOk at k
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at k
  exact ⟨Nat.pos_of_ne_zero k.1.1.1.1.1.2, Nat.pos_of_ne_zero k.1.1.1.1.2⟩

/-- **The programs' test gives the frame's test on one message, where the message is sampled.**
Conditional: ok; ha; hM: the message that the array names; hs: it has a sample. -/
theorem msgFits_of_layoutOk (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String}
    {a : ReqArray} (ha : VerifiableInference.Desc.arrayOf layout l n = some a)
    {M : Params.ReqMessage} (hM : Meaning.messageAt shape l a.message = some M)
    (hs : M.shape.answers ≠ 0) : msgFits codes shape layout l a.message = true := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  obtain ⟨m, hm, hOk⟩ := Meaning.message_of_layout ok hl (List.mem_of_find?_eq_some hf)
  obtain rfl : m = M := Option.some.inj (hm.symm.trans hM)
  obtain ⟨L, hL, hj⟩ := Option.bind_eq_some_iff.1 hM
  have e1 : shape.link.getD l default = L := by
    rw [List.getD_eq_getElem?_getD, hL]
    rfl
  have e2 : layout.link.getD l [] = as := by
    rw [List.getD_eq_getElem?_getD, hl]
    rfl
  unfold msgFits
  rw [e1, e2, hj, Option.any_some, VerifiableInference.Desc.Own.reqMessageLaid_eq, hOk,
    bne_iff_ne.2 hs, Bool.and_self, Bool.or_true]

/-- **The two public tests of the programs give the frame's test on one message.** Conditional: okS:
the test on a request's shape; ok: the test on the layout; ha. -/
theorem msgFits_of_tests (okS : reqShapeOk shape = true)
    (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String} {a : ReqArray}
    (ha : VerifiableInference.Desc.arrayOf layout l n = some a) :
    msgFits codes shape layout l a.message = true := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  obtain ⟨M, hM, -⟩ := Meaning.message_of_layout ok hl (List.mem_of_find?_eq_some hf)
  exact msgFits_of_layoutOk ok ha hM (Nat.one_le_iff_ne_zero.1 (Meaning.answers_of_shape okS hM))

/-- **THE FILLING LAYS THE ARRAY's ELEMENT AT THE RULE's PLACE**: read through the one call, at the
row and place at which the layout lays element (i, c) of the array a, the filling of the arrays'
values V answers V's value of a's name at (i, c). Conditional: ok; ha; h: where the rule forward
lays the element; hM, hs: the message is there and has a sample; hA: the address's seat; hz, hi, hc:
V has the array, and the element lies inside the size that V says. -/
theorem laidData_at (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String}
    {a : ReqArray} (ha : VerifiableInference.Desc.arrayOf layout l n = some a) {i c : ℕ}
    {p : ℕ × ℕ} (h : VerifiableInference.Desc.laidAt a i c = some p) {M : Params.ReqMessage}
    (hM : Meaning.messageAt shape l a.message = some M) (hs : M.shape.answers ≠ 0)
    {seat : MsgAddr → Option (ℕ × ℕ)} (heard : MsgAddr → ℕ) {V : ArrayVals} {A : MsgAddr}
    (hA : seat A = some (l, a.message)) {z : ℕ × ℕ} (hz : V.size l a.name = some z)
    (hi : i < z.1) (hc : c < z.2) (R : Readers) (hd : List Fmt.Drawn) :
    (laidData codes shape layout seat heard V).at_ R hd A p.1 p.2 =
      some (V.val R (hd.take (heard A)) l a.name i c) := by
  have hb := laidBack_of_laidAt ok ha h
  have hf := msgFits_of_layoutOk ok ha hM hs
  have hl : (laidData codes shape layout seat heard V).lays A p.1 p.2 = true := by
    simp only [laidData, hA, hf, hb, hz, Option.any_some, Bool.true_and, decide_eq_true_eq]
    exact ⟨hi, hc⟩
  have he : ∀ hh, (laidData codes shape layout seat heard V).entry R hh A p.1 p.2 =
      V.val R hh l a.name i c := by
    intro hh
    simp only [laidData, hA, hb]
  unfold RowData.at_
  rw [if_pos hl, he]
  rfl

/-- **THE SAME THROUGH THE CALL THAT ASKS FIRST** (`RowData.ask`): it does not reject, and answers
the arrays' value. Conditional: okS, ok: the programs' two public tests; ha; h; hA; hz, hi, hc: as
in `laidData_at`; hh: as many challenges have been heard as the sending's data reads; hr: the
values' own test says yes. -/
theorem laidData_ask (okS : reqShapeOk shape = true)
    (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String} {a : ReqArray}
    (ha : VerifiableInference.Desc.arrayOf layout l n = some a) {i c : ℕ} {p : ℕ × ℕ}
    (h : VerifiableInference.Desc.laidAt a i c = some p) {seat : MsgAddr → Option (ℕ × ℕ)}
    (heard : MsgAddr → ℕ) {V : ArrayVals} {A : MsgAddr} (hA : seat A = some (l, a.message))
    {z : ℕ × ℕ} (hz : V.size l a.name = some z) (hi : i < z.1) (hc : c < z.2) (R : Readers)
    {hd : List Fmt.Drawn} (hh : heard A ≤ hd.length)
    (hr : V.ready (hd.take (heard A)) l = true) :
    (laidData codes shape layout seat heard V).ask R hd A p.1 p.2 =
      .ok (some (V.val R (hd.take (heard A)) l a.name i c)) := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  obtain ⟨M, hM, -⟩ := Meaning.message_of_layout ok hl (List.mem_of_find?_eq_some hf)
  have hat := laidData_at ok ha h hM (Nat.one_le_iff_ne_zero.1 (Meaning.answers_of_shape okS hM))
    heard hA hz hi hc R hd
  have hfit := msgFits_of_tests okS ok ha
  have hlf : layFits shape layout = true := by
    unfold reqLayoutOk at ok
    rw [Bool.and_eq_true] at ok
    exact ok.1
  have h1 : (laidData codes shape layout seat heard V).heardOk A hd.length = true :=
    decide_eq_true hh
  have h2 : (laidData codes shape layout seat heard V).ready
      (hd.take ((laidData codes shape layout seat heard V).heardAt A)) A = true := by
    show ((seat A).all fun x => layFits shape layout && msgFits codes shape layout x.1 x.2 &&
      V.ready (hd.take (heard A)) x.1) = true
    rw [hA, Option.all_some, hlf, hfit, hr]
    rfl
  unfold RowData.ask
  rw [h1, h2, hat]
  rfl

end

/-- **`laidBack_of_seat` (WayBack.lean) with one conjunct more: the array's name.** Conditional: ok:
the programs' test on the layout; h: the cell has a seat. -/
theorem laidBack_of_seat_named {D : Sent} (ok : reqLayoutOk D.codes D.shape D.layout = true)
    {l t i c : ℕ} {s : Seat} (h : seatCalls D l (.cell t i c) = some s) :
    ∃ (bn : ℕ × String) (a : ReqArray), (D.arrayOf.getD l #[])[t]? = some bn ∧
      OnBytes.reqArray D.layout bn.1 bn.2 = some a ∧ a.name = bn.2 ∧
      laidBack D.layout bn.1 a.message s.row s.place = some (a, i, c) := by
  obtain ⟨bn, a, hbn, ha, hb⟩ := laidBack_of_seat ok h
  obtain ⟨as, -, hf⟩ := Option.bind_eq_some_iff.1 ha
  exact ⟨bn, a, hbn, ha, by simpa using List.find?_some hf, hb⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.blockBack_of_laidIn
#print axioms ProofFile.Honest.K5.sizes_of_layoutOk
#print axioms ProofFile.Honest.K5.msgFits_of_layoutOk
#print axioms ProofFile.Honest.K5.msgFits_of_tests
#print axioms ProofFile.Honest.K5.laidData_at
#print axioms ProofFile.Honest.K5.laidData_ask
#print axioms ProofFile.Honest.K5.laidBack_of_seat_named
