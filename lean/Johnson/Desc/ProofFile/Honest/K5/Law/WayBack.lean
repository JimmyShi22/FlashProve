-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/WayBack.lean: THE WAY BACK UNDOES THE LAYOUT's RULE:
CONDITIONAL on the programs' own test on a layout (`reqLayoutOk`, OnBytes/Iop/ReqRows.lean): where
the public item "layout" lays element (i, c) of an array of a segment at a row and place of an
oracle message's table, the way back from that row and place (`laidBack`,
Johnson/Desc/ProofFile/Honest/LaidData.lean) names that array and (i, c). Lemmas on public data
alone.

What it is for. The frame fills a message's main rows by the way back (`laidData`, LaidData.lean):
at a row and place it reads the value of the array's element that `laidBack` names. The verifier's
side reads a cell at the seat that the rule forward gives (`seatCalls`,
Johnson/Desc/First/Look/K3CallerAtt.lean). That the two meet at one element is this law.
LaidData.lean tests it at a toy. It serves every kind whose arrays the layout lays.

Main names:
  `blockBack_laidIn`: one block: the way back undoes the rule. Conditional: the block holds the
    element and is as large in the table as in its array.
  `blockBack_in`: where a block's way back answers, the row and place lie in its rectangle. No
    premise beside the answer.
  `arrayBack_of_laidPlace`: one array. `laidBack_of_laidPlace`: **one message of one segment.**
  `laidBack_of_laidAt`: the same in the words of Johnson/Desc/LaidAt.lean (`arrayOf`, `laidAt`).
  `laidBack_covers`: **every element inside an array's size is found by the way back**: so the
    premise «the rule forward answers» of the laws above is met there (`Meaning.laidAt_of_layout`,
    Johnson/Goal/Meaning/LaidCovered.lean).
  `back_only`: a helper: at such a row and place no other block of an array in the message answers.
  `laidBack_of_seat`: **at the seat of a cell of a segment's list of arrays**: at the
    segment that sent the array and at the array's own message.

How. At a block: the laws on an element's number in its block (`elemNo`, `elem_of`, `holds_parts`,
Johnson/Road/K4/K4PinsBlocks.lean) and `laidIn_in` (Johnson/Desc/First/Look/K3CallerLaidApart.lean).
That no other block of an array in the message answers at that row and place: the test at one
array's message and at one block (`Meaning.message_of_layout`, `Meaning.block_of_message`,
Johnson/Goal/Meaning/LaidInside.lean; `laidBlockOk`, OnBytes/Iop/ReqRows.lean), and its clause that
no two blocks meet (`tableApart_of_message`, `meets_of_point`, `one_of_flat`,
K3CallerLaidApart.lean), with `IM.findSome_only` (Johnson/IMR/LinkSeat.lean). The two writings of
the rule forward are one: `Meaning.laidPlace_eq_laidAt` (Johnson/Goal/Meaning/ReadingsOne.lean).
Kin: `laidPlace_apart` (K3CallerLaidApart.lean): two elements at one place are one.

Limits. One direction: that the rule forward undoes the way back is not shown here. The test is the
programs' `reqLayoutOk`, not the test that `laidData` asks of one message (`msgFits`,
LaidData.lean): what the first gives of the second, and what the filling then answers, stands in
WayBackFill.lean in this folder, not here. At one block the rule is the total `laidIn` of
Johnson/Desc/First/Look/K3CallerBase.lean with its test `laidHolds`; in the words of
Johnson/Desc/LaidAt.lean: WayBackFill.lean. `laidBack_of_seat` speaks at the segment that sent the
array: of a kept message's number in a later segment's list nothing is said. That the test says yes
at a description's own layout, wherever the public part is made: `Meaning.K2.pub_layoutOk`
(Johnson/IMR/LayoutOkPub.lean), not called here. Nothing on an array's values.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.LaidData
import Johnson.Desc.First.Look.K3CallerLaidApart
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Goal.Meaning.ReadingsOne
import Johnson.Goal.Meaning.LaidCovered
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open OnBytes.Road.K4 (elemNo laidIn_eq holds_parts elem_of)
open VerifiableInference.Desc.K9L (iOf cOf)
open VerifiableInference.Desc.First.Look (Sent Seat seatCalls laidHolds laidIn laidPlace laidIn_in
  meets_of_point one_of_flat tableApart_of_message)

/-- **One block: the way back undoes the rule.** Conditional: h: the block holds the element; hs: it
is as large in the table as in its array. -/
theorem blockBack_laidIn {b : LaidBlock} {i c : ℕ} (h : laidHolds b i c = true)
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) :
    blockBack b (laidIn b i c).1 (laidIn b i c).2 = some (i, c) := by
  obtain ⟨⟨r1, r2⟩, p1, p2⟩ := laidIn_in h hs
  obtain ⟨hI, hi, hC, hc⟩ := holds_parts h
  obtain ⟨hx, ei, ec⟩ := elem_of hi hc
  have ex : ((laidIn b i c).1 - b.firstRow) * 2 ^ b.placeBits +
      ((laidIn b i c).2 - b.firstPlace) = elemNo b i c := by
    rw [laidIn_eq]
    show (b.firstRow + elemNo b i c / 2 ^ b.placeBits - b.firstRow) * 2 ^ b.placeBits +
      (b.firstPlace + elemNo b i c % 2 ^ b.placeBits - b.firstPlace) = elemNo b i c
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact Nat.div_add_mod' _ _
  unfold iOf at ei
  unfold cOf at ec
  simp only [blockBack, ex]
  rw [if_pos ⟨r1, r2, p1, p2, hx⟩]
  by_cases hl : b.iIsLow = true
  · rw [if_pos hl] at ei ec ⊢
    rw [ei, ec, Nat.add_sub_cancel' hI, Nat.add_sub_cancel' hC]
  · rw [if_neg hl] at ei ec ⊢
    rw [ei, ec, Nat.add_sub_cancel' hI, Nat.add_sub_cancel' hC]

/-- Where a block's way back answers, the row and place lie in the block's rectangle. -/
theorem blockBack_in {b : LaidBlock} {r j : ℕ} {e : ℕ × ℕ} (h : blockBack b r j = some e) :
    (b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits) ∧
      b.firstPlace ≤ j ∧ j < b.firstPlace + 2 ^ b.placeBits := by
  simp only [blockBack] at h
  split at h
  · rename_i k
    exact ⟨⟨k.1, k.2.1⟩, k.2.2.1, k.2.2.2.1⟩
  · cases h

section
variable {codes : Codes} {shape : ReqShape} {layout : ReqLayout}

/-- What both laws below rest on: under the test, at the row and place at which an array's block b
lays an element, a block of an array in the same message whose way back answers is b, and its array
is that array. Conditional: ok; hl, hA: the array is one of the segment's; hb, hh: the block. -/
theorem back_only (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {as : List ReqArray}
    (hl : layout.link[l]? = some as) {a : ReqArray} (hA : a ∈ as) {b : LaidBlock}
    (hb : b ∈ a.blocks) {i c : ℕ} (hh : laidHolds b i c = true) :
    b.rowBits + b.placeBits = b.bitsI + b.bitsC ∧
      ∀ a' ∈ as.filter (fun x => x.message == a.message), ∀ b' ∈ a'.blocks, ∀ e,
        blockBack b' (laidIn b i c).1 (laidIn b i c).2 = some e → a' = a ∧ b' = b := by
  obtain ⟨m, -, hM⟩ := Meaning.message_of_layout ok hl hA
  have iA : a ∈ as.filter fun x => x.message == a.message :=
    List.mem_filter.2 ⟨hA, beq_self_eq_true _⟩
  have size : b.rowBits + b.placeBits = b.bitsI + b.bitsC := by
    obtain ⟨_, _, _, hk, _⟩ := Meaning.block_of_message hM iA hb
    unfold laidBlockOk at hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hk
    exact hk.1.1.1.1.1.1.1.1
  refine ⟨size, fun a' iA' b' hb' e he => ?_⟩
  have q := laidIn_in hh size
  have q' := blockBack_in he
  exact one_of_flat (·.blocks) _ _ (tableApart_of_message hM iA) a' iA' a iA b' hb' b hb
    (meets_of_point q' q) (meets_of_point q q')

/-- **One array: the way back undoes the rule.** Conditional: ok: the programs' test on the layout;
ha: the array of that name of that segment; h: where it lays the element. -/
theorem arrayBack_of_laidPlace (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String}
    {a : ReqArray} (ha : OnBytes.reqArray layout l n = some a) {i c : ℕ} {p : ℕ × ℕ}
    (h : laidPlace a.blocks i c = some p) : arrayBack a p.1 p.2 = some (i, c) := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  have hA : a ∈ as := List.mem_of_find?_eq_some hf
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have mb : b ∈ a.blocks := List.mem_of_find?_eq_some hb
  have hh : laidHolds b i c = true := List.find?_some (p := fun β => laidHolds β i c) hb
  obtain ⟨size, only⟩ := back_only ok hl hA mb hh
  have iA : a ∈ as.filter fun x => x.message == a.message :=
    List.mem_filter.2 ⟨hA, beq_self_eq_true _⟩
  unfold arrayBack
  rw [IM.findSome_only _ b a.blocks (fun b' hb' => ?_) mb]
  · exact blockBack_laidIn hh size
  · cases he : blockBack b' (laidIn b i c).1 (laidIn b i c).2 with
    | none => exact Or.inl rfl
    | some e => exact Or.inr (only a iA b' hb' e he).2

/-- **ONE MESSAGE OF ONE SEGMENT: THE WAY BACK NAMES THE ARRAY AND THE ELEMENT.** Conditional: as
`arrayBack_of_laidPlace`. -/
theorem laidBack_of_laidPlace (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String}
    {a : ReqArray} (ha : OnBytes.reqArray layout l n = some a) {i c : ℕ} {p : ℕ × ℕ}
    (h : laidPlace a.blocks i c = some p) :
    laidBack layout l a.message p.1 p.2 = some (a, i, c) := by
  have hB := arrayBack_of_laidPlace ok ha h
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  have hA : a ∈ as := List.mem_of_find?_eq_some hf
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have mb : b ∈ a.blocks := List.mem_of_find?_eq_some hb
  have hh : laidHolds b i c = true := List.find?_some (p := fun β => laidHolds β i c) hb
  obtain ⟨-, only⟩ := back_only ok hl hA mb hh
  have iA : a ∈ as.filter fun x => x.message == a.message :=
    List.mem_filter.2 ⟨hA, beq_self_eq_true _⟩
  have eg : layout.link.getD l [] = as := by
    rw [List.getD_eq_getElem?_getD, hl]
    rfl
  unfold laidBack
  rw [eg, IM.findSome_only _ a _ (fun a' iA' => ?_) iA, hB]
  · rfl
  · cases he : arrayBack a' (laidIn b i c).1 (laidIn b i c).2 with
    | none => exact Or.inl rfl
    | some e =>
      obtain ⟨b', hb', e'⟩ := List.exists_of_findSome?_eq_some he
      exact Or.inr (only a' iA' b' hb' e e').1

/-- The same in the words of Johnson/Desc/LaidAt.lean. Conditional: ok; ha; h. -/
theorem laidBack_of_laidAt (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String}
    {a : ReqArray} (ha : VerifiableInference.Desc.arrayOf layout l n = some a) {i c : ℕ}
    {p : ℕ × ℕ} (h : VerifiableInference.Desc.laidAt a i c = some p) :
    laidBack layout l a.message p.1 p.2 = some (a, i, c) :=
  laidBack_of_laidPlace ok (n := n) ha ((Meaning.laidPlace_eq_laidAt a i c).trans h)

/-- **EVERY ELEMENT OF EVERY ARRAY IS FOUND BY THE WAY BACK**: the rule forward answers at each
element inside the array's size, and the way back from there names the array and the element.
Conditional: ok; ha; hi, hc: the element lies inside the array's size. -/
theorem laidBack_covers (ok : reqLayoutOk codes shape layout = true) {l : ℕ} {n : String}
    {a : ReqArray} (ha : VerifiableInference.Desc.arrayOf layout l n = some a) {i c : ℕ}
    (hi : i < a.sizeI) (hc : c < a.sizeC) :
    ∃ p, VerifiableInference.Desc.laidAt a i c = some p ∧
      laidBack layout l a.message p.1 p.2 = some (a, i, c) := by
  obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 ha
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
    (Meaning.laidAt_of_layout ok hl (List.mem_of_find?_eq_some hf) hi hc)
  exact ⟨p, hp, laidBack_of_laidAt ok ha hp⟩

end

/-- **AT THE SEAT OF A CELL**: bn: the segment that sent the array of number t of segment l's list,
and its name there; a: that array. The way back, at that segment and the array's own message, from
the seat's row and place, names a and the cell. Conditional: ok: the programs' test on the layout;
h: the cell has a seat. -/
theorem laidBack_of_seat {D : Sent} (ok : reqLayoutOk D.codes D.shape D.layout = true)
    {l t i c : ℕ} {s : Seat} (h : seatCalls D l (.cell t i c) = some s) :
    ∃ (bn : ℕ × String) (a : ReqArray), (D.arrayOf.getD l #[])[t]? = some bn ∧
      OnBytes.reqArray D.layout bn.1 bn.2 = some a ∧
      laidBack D.layout bn.1 a.message s.row s.place = some (a, i, c) := by
  obtain ⟨bn, hbn, h1⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨a, ha, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨rp, hrp, h3⟩ := Option.bind_eq_some_iff.1 h2
  have key := laidBack_of_laidPlace ok ha hrp
  refine ⟨bn, a, hbn, ha, ?_⟩
  split at h3
  · obtain rfl := Option.some.inj h3
    exact key
  · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 h3
    exact key

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.blockBack_laidIn
#print axioms ProofFile.Honest.K5.blockBack_in
#print axioms ProofFile.Honest.K5.back_only
#print axioms ProofFile.Honest.K5.arrayBack_of_laidPlace
#print axioms ProofFile.Honest.K5.laidBack_of_laidPlace
#print axioms ProofFile.Honest.K5.laidBack_of_laidAt
#print axioms ProofFile.Honest.K5.laidBack_covers
#print axioms ProofFile.Honest.K5.laidBack_of_seat
