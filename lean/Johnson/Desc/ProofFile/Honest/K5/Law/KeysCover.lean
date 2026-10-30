-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeysCover.lean: NO NUMBER IN THE WITNESS IS ASKED FOR TWO
TEXTS: whatever two calls of the frame's filling (`firstData`, through `RowData.ask`) answer at one
main row and place, at two seated pairs (segment, message) with one number, is one element. These
calls are the premises of the field lays of the premise's form `LaysFilling` (LaysFilling.lean in
this folder), which this file does not import: that the form then asks one text of a number is read
off the form's text. CONDITIONAL: under the hypothesis h, the library's head on the public input
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), but for two lemmas. On public data and the readers'
letters. Five theorems.

What it is for. The form says what the witness's message with the plan's number of (l, m) holds.
Were two pairs to bear one number, it could ask one entry of one message for two values, and nothing
could meet it. This file shuts that one way of being empty. IT DOES NOT SHOW THAT THE FORM CAN BE
MET.

Main names:
  `lays_one_text`: **the sentence above.** One reader on both sides; two seats, two heards, two
    lists of challenges.
  `num_apart_head`: an array's pair (segment, the array's message) shares its number with no other
    pair.
  `ask_is_array`: whatever the filling's call that asks first (`RowData.ask`) answers at a seated
    (l, m) is the value of an array of that segment and message, at the element that the way back
    finds: the converse of `laidData_ask` (WayBackFill.lean). At all letters; no head.
  `keysCover_head`: the public test `P5T.coverB` (Johnson/P5T/KeyIsMessage.lean: every array of
    every segment has a seat with its key) accepts at the head's layout and seats.
    `keysCover_written`: it accepts at the library's written layout and seats: A CLOSED FACT,
    DECIDED BY EVALUATION IN LEAN's KERNEL.

How. `P5T.cover_gives` (KeyIsMessage.lean): under the test an array's key is listed; the plan's
number is the key's place in a list without repeats (`P5T.numOfPlan`, Johnson/P5T/NumOfPlan.lean).
To the head: `H2K5.Door.pins_at_head`, `made_row_gives`, `pseatsAll_written`, `pseatsAllW_is`
(Johnson/Desc/First/Att/Door/Law/: K5CondOfHead.lean, K5Written.lean, K5WrittenAll.lean,
K5WrittenIsFull.lean). Kin: `P5T.key_of_num` (Johnson/P5T/KeyBack.lean); `P5J.key_there`
(Johnson/HB/LLHARD/MaskSeatWritten.lean), the like at one key.

Limits. One of the two pairs is an array's: of two messages in neither of which the layout lays an
array nothing is said; the form asks nothing there (`ask_is_array`). `num_apart_head` speaks of
pairs (segment, message): a message that is no segment's own has a number of its own in the same
list (`P5T.keyOf`, `P5T.arrOf`): of these nothing is said. One row and place, in the main rows. What
another kind's form may ask of the same message at other places is not spoken of.
`keysCover_written` has been checked by Lean's own kernel alone; `keysCover_head`, `num_apart_head`
and `lays_one_text` rest on it and on the head's comparison with the library's written values.
Through its imports the file stands above Cb/Bridge/CodeListRSProved.lean, and so above the files
under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.P5T.KeyIsMessage
import Johnson.P5T.PlanSeatsFull
import Johnson.G.LayoutLit
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.Desc.First.Att.Door.Law.K5WrittenIsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K1 (cellsVals firstData)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **At the library's written layout and seats every array has a seat with its key.** By evaluation
in Lean's kernel. -/
theorem keysCover_written : P5T.coverB Johnson.G.layoutFull P5T.seatsAllFull = true := by
  decide +kernel

/-- **WHAT THE CALL THAT ASKS FIRST ANSWERS IS AN ARRAY's VALUE.** Conditional: hAd: the address's
seat; q: the call answers the element y. -/
theorem ask_is_array {codes : OnBytes.Codes} {shape : OnBytes.Params.ReqShape}
    {layout : OnBytes.Params.ReqLayout} {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ}
    {V : ArrayVals} {R : Readers} {hd : List Fmt.Drawn} {Ad : MsgAddr} {l m row place : ℕ}
    {y : Cb.Gl.F ⊕ Cb.Gl.E} (hAd : seat Ad = some (l, m))
    (q : (laidData codes shape layout seat heard V).ask R hd Ad row place = .ok (some y)) :
    ∃ (A : OnBytes.Params.ReqArray) (i c : ℕ), A ∈ layout.link.getD l [] ∧ A.message = m ∧
      laidBack layout l m row place = some (A, i, c) ∧
      y = V.val R (hd.take (heard Ad)) l A.name i c := by
  unfold RowData.ask at q
  split at q
  · cases q
  · split at q
    · cases q
    · have q1 := Except.ok.inj q
      unfold RowData.at_ at q1
      split at q1
      · rename_i hlay
        have ey := Option.some.inj q1
        simp only [laidData, hAd] at hlay ey
        rw [Bool.and_eq_true] at hlay
        cases hB : laidBack layout l m row place with
        | none =>
          rw [hB] at hlay
          exact absurd hlay.2 (by simp)
        | some w =>
          obtain ⟨A, i, c⟩ := w
          rw [hB] at ey
          have hB' := hB
          unfold laidBack at hB'
          obtain ⟨a, ha, hmap⟩ := List.exists_of_findSome?_eq_some hB'
          obtain ⟨pq, -, e⟩ := Option.map_eq_some_iff.1 hmap
          obtain rfl : a = A := (Prod.mk.inj e).1
          have hmem := List.mem_filter.1 ha
          exact ⟨a, i, c, hmem.1, beq_iff_eq.1 hmem.2, rfl, ey.symm⟩
      · cases q1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The same test at the head's layout and seats.** CONDITIONAL: under the hypothesis h. -/
theorem keysCover_head : P5T.coverB h.𝔇.sent.layout (P5J.At.pseatsAll Zp) = true := by
  have hm := (H2K5.Door.pins_at_head h.toAtMg).1
  obtain ⟨-, -, -, -, -, f6⟩ := (H2K5.Door.made_row_gives hm).1
  have e1 : h.𝔇.sent.layout = Johnson.G.layoutFull := f6
  rw [e1, H2K5.Door.pseatsAll_written h.toAtMg hm, H2K5.Door.pseatsAllW_is]
  exact keysCover_written

/-- **AN ARRAY's PAIR SHARES ITS NUMBER WITH NO OTHER PAIR.** CONDITIONAL: under the hypothesis h; A
is an array of segment l; its message and message m' of segment l' bear one number in the
witness. -/
theorem num_apart_head {l l' m' : ℕ} {As : List OnBytes.Params.ReqArray}
    {A : OnBytes.Params.ReqArray} (hl : h.𝔇.sent.layout.link[l]? = some As) (hA : A ∈ As)
    (e : P5J.At.num Zp l A.message = P5J.At.num Zp l' m') : l = l' ∧ A.message = m' := by
  obtain ⟨p, hp, hk, -, -⟩ := P5T.cover_gives (keysCover_head h) hl hA
  have h1 : (0, l, A.message) ∈ ((P5J.At.pseatsAll Zp).map P5T.keyOf).eraseDups :=
    List.mem_eraseDups.2 (List.mem_map.2 ⟨p, hp, hk⟩)
  have e' : (((P5J.At.pseatsAll Zp).map P5T.keyOf).eraseDups).idxOf (0, l, A.message) =
      (((P5J.At.pseatsAll Zp).map P5T.keyOf).eraseDups).idxOf (0, l', m') := e
  have k := (List.idxOf_inj h1).1 e'
  exact ⟨(Prod.mk.inj (Prod.mk.inj k).2).1, (Prod.mk.inj (Prod.mk.inj k).2).2⟩

/-- **THE FORM ASKS NO NUMBER FOR TWO TEXTS.** CONDITIONAL: under the hypothesis h; the two
addresses' seats; both calls answer an element at one row and place; the two pairs bear one number
in the witness. -/
theorem lays_one_text {seat seat' : MsgAddr → Option (ℕ × ℕ)} {heard heard' : MsgAddr → ℕ}
    {R : Readers} {hd hd' : List Fmt.Drawn} {Ad Ad' : MsgAddr} {l m l' m' row place : ℕ}
    {y y' : Cb.Gl.F ⊕ Cb.Gl.E} (hAd : seat Ad = some (l, m)) (hAd' : seat' Ad' = some (l', m'))
    (q : (firstData Sz.ref h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat heard).ask R hd Ad row
      place = .ok (some y))
    (q' : (firstData Sz.ref h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat' heard').ask R hd'
      Ad' row place = .ok (some y'))
    (e : P5J.At.num Zp l m = P5J.At.num Zp l' m') : y = y' := by
  obtain ⟨A, i, c, hA, hm, hB, ey⟩ := ask_is_array hAd q
  obtain ⟨A', i', c', -, -, hB', ey'⟩ := ask_is_array hAd' q'
  have mem : ∀ {l₀ : ℕ} {B : OnBytes.Params.ReqArray}, B ∈ h.𝔇.sent.layout.link.getD l₀ [] →
      ∃ As, h.𝔇.sent.layout.link[l₀]? = some As ∧ B ∈ As := by
    intro l₀ B hBm
    rw [List.getD_eq_getElem?_getD] at hBm
    cases hq : h.𝔇.sent.layout.link[l₀]? with
    | none =>
      rw [hq] at hBm
      exact absurd hBm (by simp)
    | some As =>
      rw [hq] at hBm
      exact ⟨As, rfl, hBm⟩
  obtain ⟨As, hl, hAs⟩ := mem hA
  obtain ⟨rfl, e2⟩ := num_apart_head h (l' := l') (m' := m') hl hAs (by rw [hm]; exact e)
  obtain rfl : m = m' := by rw [← hm]; exact e2
  obtain ⟨rfl, rfl, rfl⟩ : A = A' ∧ i = i' ∧ c = c' := by
    have k := Option.some.inj (hB.symm.trans hB')
    exact ⟨(Prod.mk.inj k).1, (Prod.mk.inj (Prod.mk.inj k).2).1, (Prod.mk.inj (Prod.mk.inj k).2).2⟩
  rw [ey, ey']
  rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.keysCover_written
#print axioms ProofFile.Honest.K5.ask_is_array
#print axioms ProofFile.Honest.K5.keysCover_head
#print axioms ProofFile.Honest.K5.num_apart_head
#print axioms ProofFile.Honest.K5.lays_one_text
