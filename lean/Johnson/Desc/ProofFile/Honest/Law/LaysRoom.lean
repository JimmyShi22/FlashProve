-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaysRoom.lean: WHERE THE FILLING laidData (Honest/LaidData.lean)
LAYS AN ELEMENT THERE IS ROOM, OFF THE PAD: the place lies in a main row that is sent, below the
base code's message length, and is no place of the pad of the message's sample. THE JOIN from the
plan's own test on a message's arrays (Own.reqMessageLaid, Johnson/Desc/Own/Req.lean) to the
filling's "lays", to padInMain and RowData.clear (Honest/RowData.lean), and to the library's plain
test padB (Johnson/Desc/SeatAt.lean). Statements and proofs; no definition. PUBLIC: no coin, no
witness, no input.

  back_in_block   what the way back answers lies in the laid block's rectangle (forward: the
                library's laidIn_rect)
  padInMain_pad   the list padInMain of the pad's places in a main row is among the programs' own
                (Send.pad, where that returns a list), entry by entry, at any number of answers
  block_room    THE JOIN, AT A LAID BLOCK, BACKWARD
  lays_room     where the filling lays, under codes.lengthsOk: a row that is sent; a place below the
                length; off the pad; in a sampled message
  laidAt_room   block_room's three (row, place, off the pad) forward, at the library's own laidAt,
                in padInMain's form
  clear_laid    RowData.clear holds at every address with a seat in the shape's list, under
                codes.lengthsOk
  padB_of_room  a place below the length and off padInMain, in a sampled message, is none of padB's
  lays_off_padB   so in padB's form
  msgFits_of_plan   the programs' tests on shape and layout give msgFits at every message of the
                shape

WHAT IS CALLED, NOT STATED AGAIN. THE FORWARD FORM IS IN THE LIBRARY:
Johnson/Goal/Meaning/LaidInside.lean: laidAt_geometry, laidAt_inside; at a made public part
Johnson/P5J/InsideAtPure.lean: inside_at_pure. This file calls that file's block_of_message,
covers_of_rect, aligned_inside, le_pow_ceil, ell_pow, answers_of_shape (at its messageAt); and Own's
test on a message is the programs' by reqMessageLaid_eq (Johnson/Desc/Own/ReqAgree.lean). FURTHER
KIN, FORWARD, UNDER OTHER TESTS, NOT CALLED: laidPlace_some
(Johnson/Desc/First/Look/K3CallerLaid.lean) under blocksB; padB_off
(Johnson/Desc/Kinds/Law/LaidOffPad.lean) under missB. WHAT IS NEW: THE WAY BACK (blockBack, "lays"),
padInMain, RowData.clear, msgFits.

THE PREMISE codes.lengthsOk. The test on a layout holds the laid blocks inside a table of 2 ^ logEll
places, and Code.logEll is the rounded-up logarithm: only where the length is a power of two is that
the length. (So the library's laidAt_inside: "each of the three tests is needed".) codes.lengthsOk
is a premise of block_room, lays_room, laidAt_room, clear_laid and lays_off_padB.

Limits. Of the layout and the shapes alone: that a program lays as the layout says is not said. The
shape and the codes are the list's and the plan's: that a sender's are these is not said here.
Nothing of a pad in a mask row: padInMain is empty there. padB says of itself "at one answer". On
hiding nothing is said. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaidBack
import Johnson.Goal.Meaning.LaidInside
import Johnson.Desc.Own.ReqAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc (laidIn laidAt padB)
open VerifiableInference.Desc.Own (reqMessageLaid reqLayoutFits reqMessageLaid_eq)

/-- What the way back answers lies in the laid block's rectangle. -/
theorem back_in_block (b : LaidBlock) {r j : Nat} {e : Nat × Nat} (h : blockBack b r j = some e) :
    b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits ∧ b.firstPlace ≤ j ∧
      j < b.firstPlace + 2 ^ b.placeBits := by
  unfold blockBack at h
  simp only at h
  split at h
  · rename_i hh
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
  · cases h

/-- The list padInMain of the pad's places in a main row is among the programs' own (Send.pad, where
that returns a list), entry by entry. -/
theorem padInMain_pad (codes : OnBytes.Codes) (o : OnBytes.OracleShape)
    {pad : List OnBytes.PadPlace} (h : OnBytes.Send.pad codes o = some pad) {r j : Nat}
    (hp : (r, j) ∈ padInMain (codes.base.getD o.code default).ell o) :
    ∃ p ∈ pad, p.part = .main ∧ p.index = r + j * 2 ^ OnBytes.ceilLog2 o.mainRows := by
  unfold padInMain at hp
  split at hp
  · cases hp
  · rename_i hg
    simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, not_or, ne_eq, Decidable.not_not] at hg
    obtain ⟨hk, hm⟩ := hg
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hp
    obtain ⟨i, hi, hr, hj⟩ := hp
    have hm0 : 0 < o.mainRows := Nat.pos_of_ne_zero hm
    have core : ∀ each : Nat, 0 < each → i < each * o.answers →
        (codes.base.getD o.code default).ell - each * o.answers + i = j →
        (if (codes.base.getD o.code default).ell < each * o.answers then none
          else some ((List.range o.answers).flatMap fun i' => (List.range each).map fun t =>
            ({ part := .main
               index := o.mainRows - 1 + ((codes.base.getD o.code default).ell - each * o.answers +
                 each * i' + t) * 2 ^ OnBytes.ceilLog2 o.mainRows
               answer := i'
               basis := OnBytes.thetaE t } : OnBytes.PadPlace))) = some pad →
        ∃ p ∈ pad, p.part = .main ∧ p.index = r + j * 2 ^ OnBytes.ceilLog2 o.mainRows := by
      intro each he0 hi hj h
      split at h
      · cases h
      · cases h
        refine ⟨_, List.mem_flatMap.2 ⟨i / each, List.mem_range.2 (Nat.div_lt_of_lt_mul hi),
          List.mem_map.2 ⟨i % each, List.mem_range.2 (Nat.mod_lt _ he0), rfl⟩⟩, rfl, ?_⟩
        show o.mainRows - 1 + ((codes.base.getD o.code default).ell - each * o.answers +
          each * (i / each) + i % each) * 2 ^ OnBytes.ceilLog2 o.mainRows = _
        rw [← hr, ← hj, Nat.add_assoc, Nat.div_add_mod]
    unfold OnBytes.Send.pad OnBytes.Send.cube at h
    simp only [hk, Nat.lt_irrefl, decide_false, Bool.false_eq_true, if_false, Bool.false_or, hm0,
      decide_true, if_true] at h
    by_cases h3 : (o.mainDeg == 3) = true
    · simp only [h3, if_true] at h hi hj
      exact core 1 (by decide) hi hj h
    · simp only [h3, if_false, Bool.false_eq_true] at h hi hj
      exact core 3 (by decide) hi hj h

/-- **THE JOIN, AT A LAID BLOCK**: under the plan's own test on a message's arrays, at codes whose
lengths are powers of two. -/
theorem block_room (codes : OnBytes.Codes) (o : OnBytes.OracleShape) (L : List ReqArray)
    (hfit : reqMessageLaid codes o L = true) (hlen : codes.lengthsOk = true) {A : ReqArray}
    {b : LaidBlock} (hA : A ∈ L) (hb : b ∈ A.blocks) {r j : Nat} {e : Nat × Nat}
    (h : blockBack b r j = some e) :
    r < o.mainRows ∧ j < (codes.base.getD o.code default).ell ∧
      (r, j) ∉ padInMain (codes.base.getD o.code default).ell o := by
  have R := back_in_block b h
  rw [reqMessageLaid_eq] at hfit
  obtain ⟨pad, hc, hpd, hok, hrow, hoff⟩ := Meaning.block_of_message hfit hA hb
  simp only [OnBytes.laidBlockOk, OnBytes.laidAligned, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, k3⟩, -⟩, -⟩, -⟩, k7⟩, -⟩, k9⟩ := hok
  have hr : r < o.mainRows := Nat.lt_of_lt_of_le R.2.1 hrow
  have hj : j < (codes.base.getD o.code default).ell := by
    rw [← Meaning.ell_pow hlen hc]
    exact Nat.lt_of_lt_of_le R.2.2.2 (Meaning.aligned_inside k3 k7.2 k9)
  refine ⟨hr, hj, fun hp => ?_⟩
  obtain ⟨p, hpm, hpp, hpi⟩ := padInMain_pad codes o hpd hp
  have q := Meaning.covers_of_rect (Nat.lt_of_lt_of_le hr (Meaning.le_pow_ceil _)) R
  rw [← hpi, hoff p hpm hpp] at q
  cases q

/-- **WHERE THE FILLING LAYS, THERE IS ROOM, OFF THE PAD, IN A SAMPLED MESSAGE**: at codes whose
lengths are powers of two (codes.lengthsOk), at an address with a seat in the shape's list. -/
theorem lays_room (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals)
    (hlen : codes.lengthsOk = true) {a : MsgAddr} {l m r j : Nat} {M : OnBytes.Params.ReqMessage}
    (hs : seat a = some (l, m)) (hM : (s.link.getD l default).messages[m]? = some M)
    (h : (laidData codes s lay seat heard V).lays a r j = true) :
    r < M.shape.mainRows ∧ j < (codes.base.getD M.shape.code default).ell ∧
      (r, j) ∉ padInMain (codes.base.getD M.shape.code default).ell M.shape ∧
      M.shape.answers ≠ 0 := by
  have h' : (msgFits codes s lay l m && (laidBack lay l m r j).any fun x =>
      (V.size l x.1.name).any fun z => decide (x.2.1 < z.1 ∧ x.2.2 < z.2)) = true := by
    have q := h
    unfold laidData at q
    simp only [hs] at q
    exact q
  rw [Bool.and_eq_true] at h'
  obtain ⟨hfit, hany⟩ := h'
  cases hb : laidBack lay l m r j with
  | none =>
    rw [hb] at hany
    cases hany
  | some x =>
    unfold laidBack at hb
    obtain ⟨A, hA, hA2⟩ := List.exists_of_findSome?_eq_some hb
    cases hab : arrayBack A r j with
    | none =>
      rw [hab] at hA2
      cases hA2
    | some e =>
      unfold arrayBack at hab
      obtain ⟨b, hbm, hbb⟩ := List.exists_of_findSome?_eq_some hab
      unfold msgFits at hfit
      rw [hM] at hfit
      have hne : ((lay.link.getD l []).filter fun a => a.message == m).isEmpty = false := by
        cases hl : (lay.link.getD l []).filter fun a => a.message == m with
        | nil =>
          rw [hl] at hA
          cases hA
        | cons _ _ => rfl
      simp only [Option.any_some, hne, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq] at hfit
      obtain ⟨q1, q2, q3⟩ := block_room codes M.shape _ hfit.2 hlen hA hbm hbb
      exact ⟨q1, q2, q3, hfit.1⟩

/-- block_room's three (a row that is sent, a place below the length, off padInMain's places)
FORWARD, at the library's own laidAt, under block_room's two premises. BESIDE THE LIBRARY's
laidAt_geometry: that law speaks under the test on a whole layout and ends at the indices of
Send.pad; this one speaks under the test on ONE message's arrays, which is what msgFits holds, and
ends in padInMain's form, which is what RowData.clear and the callers' premises read. -/
theorem laidAt_room (codes : OnBytes.Codes) (o : OnBytes.OracleShape) (L : List ReqArray)
    (hfit : reqMessageLaid codes o L = true) (hlen : codes.lengthsOk = true) {A : ReqArray}
    (hA : A ∈ L) {i c : Nat} {rp : Nat × Nat} (h : laidAt A i c = some rp) :
    rp.1 < o.mainRows ∧ rp.2 < (codes.base.getD o.code default).ell ∧
      rp ∉ padInMain (codes.base.getD o.code default).ell o := by
  unfold laidAt at h
  obtain ⟨b, hb, hbi⟩ := List.exists_of_findSome?_eq_some h
  -- the laid block is as large in the table as in its array
  have hev : b.rowBits + b.placeBits = b.bitsI + b.bitsC := by
    have q := hfit
    rw [reqMessageLaid_eq] at q
    obtain ⟨_, -, -, hok, -, -⟩ := Meaning.block_of_message q hA hb
    simp only [OnBytes.laidBlockOk, Bool.and_eq_true, beq_iff_eq] at hok
    exact hok.1.1.1.1.1.1.1.1
  exact block_room codes o L hfit hlen hA hb (back_of_place b hev (i := i) (c := c)
    (r := rp.1) (j := rp.2) hbi)

/-- **THE SEAT's TEST HOLDS**: at every address with a seat in the shape's list, at codes whose
lengths are powers of two (codes.lengthsOk). -/
theorem clear_laid (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals)
    (hlen : codes.lengthsOk = true) {a : MsgAddr} {l m : Nat} {M : OnBytes.Params.ReqMessage}
    (hs : seat a = some (l, m)) (hM : (s.link.getD l default).messages[m]? = some M) :
    (laidData codes s lay seat heard V).clear a (codes.base.getD M.shape.code default).ell
      M.shape = true := by
  have key : ∀ r j, (r, j) ∈ padInMain (codes.base.getD M.shape.code default).ell M.shape ∨
      M.shape.mainRows ≤ r ∨ (codes.base.getD M.shape.code default).ell ≤ j →
      (laidData codes s lay seat heard V).lays a r j = false := by
    intro r j hc
    cases hl : (laidData codes s lay seat heard V).lays a r j with
    | false => rfl
    | true =>
      obtain ⟨q1, q2, q3, -⟩ := lays_room codes s lay seat heard V hlen hs hM hl
      rcases hc with hc | hc | hc
      · exact absurd hc q3
      · omega
      · omega
  unfold RowData.clear
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨fun p hp => key p.1 p.2 (Or.inl hp), key _ _ (Or.inr (Or.inl (Nat.le_refl _)))⟩,
    fun r _ => key _ _ (Or.inr (Or.inr (Nat.le_refl _)))⟩

/-- A place below the length and off padInMain, in a sampled message, is none of padB's. -/
theorem padB_of_room (codes : OnBytes.Codes) (o : OnBytes.OracleShape) {r j : Nat}
    (q2 : j < (codes.base.getD o.code default).ell)
    (q3 : (r, j) ∉ padInMain (codes.base.getD o.code default).ell o) (q4 : o.answers ≠ 0) :
    padB codes o false r j = false := by
  cases hp : padB codes o false r j with
  | false => rfl
  | true =>
    exfalso
    apply q3
    unfold padB at hp
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hp
    obtain ⟨⟨hk, hr⟩, hj⟩ := hp
    unfold padInMain
    have hg : (o.maskRows != 0 || o.mainRows == 0) = false := by
      rw [hk]
      have : o.mainRows ≠ 0 := by omega
      simp [this]
    rw [hg]
    simp only [Bool.false_eq_true, if_false, List.mem_map, List.mem_range, Prod.mk.injEq]
    have ha : 1 ≤ o.answers := Nat.pos_of_ne_zero q4
    by_cases h3 : o.mainDeg = 3
    · have e3 : (if (o.mainDeg == 3) = true then 1 else 3) = 1 := by simp [h3]
      rw [if_pos h3] at hj
      rw [e3]
      exact ⟨j - ((codes.base.getD o.code default).ell - 1 * o.answers), by omega, by omega,
        by omega⟩
    · have e3 : (if (o.mainDeg == 3) = true then 1 else 3) = 3 := by simp [h3]
      rw [if_neg h3] at hj
      rw [e3]
      exact ⟨j - ((codes.base.getD o.code default).ell - 3 * o.answers), by omega, by omega,
        by omega⟩

/-- In the library's plain test's form. (padB says of itself: at one answer; its places are the last
answer's.) -/
theorem lays_off_padB (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat) (V : ArrayVals)
    (hlen : codes.lengthsOk = true) {a : MsgAddr} {l m r j : Nat} {M : OnBytes.Params.ReqMessage}
    (hs : seat a = some (l, m)) (hM : (s.link.getD l default).messages[m]? = some M)
    (h : (laidData codes s lay seat heard V).lays a r j = true) :
    padB codes M.shape false r j = false := by
  obtain ⟨-, q2, q3, q4⟩ := lays_room codes s lay seat heard V hlen hs hM h
  exact padB_of_room _ _ q2 q3 q4

/-- The programs' tests on shape and layout give msgFits at every message of the shape. -/
theorem msgFits_of_plan (codes : OnBytes.Codes) (s : ReqShape) (lay : ReqLayout)
    (hsh : OnBytes.reqShapeOk s = true) (hl : reqLayoutFits codes s lay = true) {l m : Nat}
    (hm : m < (s.link.getD l default).messages.length) : msgFits codes s lay l m = true := by
  have hl' : l < s.link.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hc)] at hm
    exact absurd hm (Nat.not_lt_zero _)
  unfold reqLayoutFits at hl
  rw [Bool.and_eq_true, beq_iff_eq, OnBytes.zipT_eq, List.all_eq_true] at hl
  obtain ⟨hlen, hall⟩ := hl
  have hl2 : l < lay.link.length := by omega
  have e1 : s.link.getD l default = s.link[l] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl']
    rfl
  have e2 : lay.link.getD l [] = lay.link[l] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl2]
    rfl
  have hz : (s.link[l], lay.link[l]) ∈ s.link.zip lay.link := by
    have q : (s.link.zip lay.link)[l]? = some (s.link[l], lay.link[l]) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hl', List.getElem?_eq_getElem hl2⟩
    exact List.mem_of_getElem? q
  have hx := hall _ hz
  simp only [Bool.and_eq_true, List.all_eq_true] at hx
  rw [e1] at hm
  have hmz : (s.link[l].messages[m], m) ∈ s.link[l].messages.zipIdx :=
    List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hm)
  have hfit := hx.2 _ hmz
  -- every message of a link is sampled: the library's law
  have hat : Meaning.messageAt s l m = some s.link[l].messages[m] := by
    unfold Meaning.messageAt
    rw [List.getElem?_eq_getElem hl']
    exact List.getElem?_eq_getElem hm
  have hans := Meaning.answers_of_shape hsh hat
  unfold msgFits
  rw [e1, e2, List.getElem?_eq_getElem hm]
  simp only [Option.any_some, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact Or.inr ⟨by omega, hfit⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.back_in_block
#print axioms ProofFile.Honest.padInMain_pad
#print axioms ProofFile.Honest.block_room
#print axioms ProofFile.Honest.lays_room
#print axioms ProofFile.Honest.laidAt_room
#print axioms ProofFile.Honest.clear_laid
#print axioms ProofFile.Honest.padB_of_room
#print axioms ProofFile.Honest.lays_off_padB
#print axioms ProofFile.Honest.msgFits_of_plan
