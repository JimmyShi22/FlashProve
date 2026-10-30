-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LaidInside.lean: what the programs' test on a layout says of the seat at which
an array's element lies. Theorems, proved.

Why. The plan's item "layout" says in which rectangles of which oracle message every array of every
link lies. laidAt (Johnson/Desc/LaidAt.lean) reads it: array, row, column ↦ the message's main row
and place: the element's seat. The programs test a layout before they use it: reqLayoutOk
(OnBytes/Iop/ReqRows.lean), a Bool. That test speaks of BLOCKS: each is aligned, lies inside its
message's table and in rows that are sent, and covers no place of the pad of the message's sample
(Send.pad, OnBytes/Iop/Send.lean). Whoever reads a witness at the seats needs the same of the
SEATS. This file leads from the Bool to the seats.

Main names:
  laidIn_rect   where a block holds an element lies in the block's rectangle.
  message_of_layout, block_of_message   the test, unpacked at one array and at one block.
  messageAt shape l j   message j of link l of a request's shape.
  laidAt_geometry   THE GEOMETRY IN THE PROGRAMS' OWN LETTERS: reqLayoutOk codes shape layout =
    true, A an array of link l, laidAt A i c = some (r, p). Then the message m that A names is
    there, its sample has a pad, its main code is there, r < m.shape.mainRows, p < 2 ^ logEll of
    that code, and no main place of the pad has the index r + p * 2 ^ ceilLog2 m.shape.mainRows.
  pad_of_padB, padB_of_pad   padB (Johnson/Desc/SeatAt.lean) against Send.pad. padB says of itself
    "at one answer". With s answers Send.pad has s times as many places. Forth: from one answer on,
    a place inside the row that padB takes for a pad's main place is a main place of Send.pad (the
    last answer's). Back: at one answer every main place of Send.pad is one of padB's.
  ell_pow, answers_of_shape   what the tests Codes.lengthsOk (OnBytes/Iop/Ground.lean) and
    reqShapeOk (OnBytes/Iop/Req.lean) give: a main code's length is 2 ^ logEll; every message of
    every link has an answer. shapeOk_of_reqOk: reqOk holds reqShapeOk.
  laidAt_inside   THE GEOMETRY AS A WITNESS's ACCESSOR READS IT: under the three tests: r <
    m.shape.mainRows, p < the main code's length, padB codes m.shape false r p = false.

Object, user, letters.
  laidAt_geometry   object: reqLayoutOk, laidAt, Send.pad. User: laidAt_inside. Letters: all free.
  laidAt_inside   object: these and Codes.lengthsOk, reqShapeOk, padB. User: array_inside
    (Johnson/Goal/Meaning/LaidInsideSeats.lean). Letters: all free.
Each of the three tests is needed, and all premises hold together somewhere:
Johnson/Goal/Meaning/LaidInsideMember.lean [not in this library].

Two small lemmas are typed again here, so that this file stands on the programs' text and on two
files of definitions alone: le_pow_ceil (so OnBytes.Slice.le_two_pow_ceilLog2,
OnBytes/Slice/ProgCodes.lean) and ell_pow (so pow_logEll, Johnson/Desc/K1/Law/When.lean).

What is not claimed. That laidAt answers at every element of an array: the test has the cover by
counting; no theorem here says it, and every statement here speaks of a seat that is there. That two
elements have two seats. Anything of mask rows. That the codes, the shape or the layout of any plan
pass the tests: none has run here. That a witness's message has the shape m.shape. Nothing on
soundness, nothing on hiding. The program does not import this file.
-/
import OnBytes.Iop.ReqRows
import Johnson.Desc.LaidAt
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning

open OnBytes
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape ReqMessage)
open VerifiableInference.Desc (laidIn laidAt padB)

/-! ## Numbers -/

/-- Digit y above digit x: below the product of the two ranges. -/
theorem number_lt {a b x y : Nat} (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    y * 2 ^ a + x < 2 ^ (a + b) := by
  have h : (y + 1) * 2 ^ a ≤ 2 ^ b * 2 ^ a := Nat.mul_le_mul_right _ hy
  rw [Nat.add_mul, Nat.one_mul] at h
  rw [Nat.pow_add, Nat.mul_comm (2 ^ a) (2 ^ b)]
  omega

/-- An aligned stretch that begins inside an aligned range ends inside it. -/
theorem aligned_inside {f a T : Nat} (ha : a ≤ T) (hal : f % 2 ^ a = 0) (hf : f < 2 ^ T) :
    f + 2 ^ a ≤ 2 ^ T := by
  obtain ⟨q, rfl⟩ : ∃ q, f = 2 ^ a * q :=
    ⟨f / 2 ^ a, by have := Nat.div_add_mod f (2 ^ a); omega⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [Nat.pow_add] at hf ⊢
  have hq : q + 1 ≤ 2 ^ d := Nat.lt_of_mul_lt_mul_left hf
  have h := Nat.mul_le_mul_left (2 ^ a) hq
  rw [Nat.mul_add, Nat.mul_one] at h
  exact h

/-- n is at most 2 ^ ceilLog2 n. -/
theorem le_pow_ceil (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split
  · omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-! ## One block -/

/-- **Where a block holds an element lies in the block's rectangle.** -/
theorem laidIn_rect {b : LaidBlock} {i c r p : Nat}
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) (h : laidIn b i c = some (r, p)) :
    b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits ∧
      b.firstPlace ≤ p ∧ p < b.firstPlace + 2 ^ b.placeBits := by
  unfold laidIn at h
  split at h
  · rename_i hin
    obtain ⟨h1, h2, h3, h4⟩ := hin
    obtain ⟨x, hx, rfl, rfl⟩ : ∃ x, x < 2 ^ (b.placeBits + b.rowBits) ∧
        r = b.firstRow + x / 2 ^ b.placeBits ∧ p = b.firstPlace + x % 2 ^ b.placeBits := by
      have e := Option.some.inj h
      refine ⟨_, ?_, (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
      rw [Nat.add_comm b.placeBits b.rowBits, hs]
      split
      · exact number_lt (a := b.bitsI) (b := b.bitsC) (by omega) (by omega)
      · rw [Nat.add_comm b.bitsI b.bitsC]
        exact number_lt (a := b.bitsC) (b := b.bitsI) (by omega) (by omega)
    have d : x / 2 ^ b.placeBits < 2 ^ b.rowBits := by
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add]
      exact hx
    have m : x % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ (Nat.two_pow_pos _)
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left d _, Nat.le_add_right _ _,
      Nat.add_lt_add_left m _⟩
  · cases h

/-- A place of the block's rectangle, in a row below 2 ^ R, is covered by the block. -/
theorem covers_of_rect {b : LaidBlock} {R r p : Nat} (hr : r < 2 ^ R)
    (h : b.firstRow ≤ r ∧ r < b.firstRow + 2 ^ b.rowBits ∧
      b.firstPlace ≤ p ∧ p < b.firstPlace + 2 ^ b.placeBits) :
    laidCovers b R (r + p * 2 ^ R) = true := by
  have e1 : (r + p * 2 ^ R) % 2 ^ R = r := by
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt hr
  have e2 : (r + p * 2 ^ R) / 2 ^ R = p := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos R), Nat.div_eq_of_lt hr, Nat.zero_add]
  unfold laidCovers
  simp only [e1, e2, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

/-- An array holds an element by one of its blocks. -/
theorem laidAt_block {A : ReqArray} {i c : Nat} {x : Nat × Nat} (h : laidAt A i c = some x) :
    ∃ b ∈ A.blocks, laidIn b i c = some x :=
  List.exists_of_findSome?_eq_some h

/-! ## What the test says of one block -/

/-- Message j of link l of a request's shape. -/
def messageAt (shape : ReqShape) (l j : Nat) : Option ReqMessage :=
  (shape.link[l]?).bind fun L => L.messages[j]?

/-- The test on a layout, at one array of one link: the message that the array names is there, and
the arrays that lie in it fit it. -/
theorem message_of_layout {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (h : reqLayoutOk codes shape layout = true) {l : Nat} {as : List ReqArray}
    (hl : layout.link[l]? = some as) {A : ReqArray} (hA : A ∈ as) :
    ∃ m, messageAt shape l A.message = some m ∧
      reqMessageLayoutOk codes m.shape (as.filter fun a => a.message == A.message) = true := by
  unfold reqLayoutOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, zipT_eq, decide_eq_true_eq] at h
  obtain ⟨hlen, hall⟩ := h
  obtain ⟨hl1, hl2⟩ := List.getElem?_eq_some_iff.1 hl
  have hl3 : l < shape.link.length := hlen ▸ hl1
  have hmem : (shape.link[l], as) ∈ shape.link.zip layout.link := by
    have hz : l < (shape.link.zip layout.link).length := by
      rw [List.length_zip]
      omega
    have e : (shape.link.zip layout.link)[l] = (shape.link[l], as) := by
      rw [List.getElem_zip, hl2]
    exact e ▸ List.getElem_mem hz
  obtain ⟨⟨⟨-, h2⟩, -⟩, h4⟩ := hall _ hmem
  have hj : A.message < (shape.link[l]).messages.length := h2 A hA
  refine ⟨(shape.link[l]).messages[A.message], ?_, ?_⟩
  · unfold messageAt
    rw [List.getElem?_eq_getElem hl3, Option.bind_some, List.getElem?_eq_getElem hj]
  · exact h4 ((shape.link[l]).messages[A.message], A.message)
      (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hj))

/-- The test on one message's arrays, at one block of one of them. -/
theorem block_of_message {codes : Codes} {o : OracleShape} {inIt : List ReqArray}
    (h : reqMessageLayoutOk codes o inIt = true) {A : ReqArray} (hA : A ∈ inIt) {b : LaidBlock}
    (hb : b ∈ A.blocks) :
    ∃ pad, o.code < codes.base.size ∧ Send.pad codes o = some pad ∧
      laidBlockOk b (ceilLog2 o.mainRows) (codes.base.getD o.code default).logEll = true ∧
      b.firstRow + 2 ^ b.rowBits ≤ o.mainRows ∧
      ∀ q ∈ pad, q.part = .main → laidCovers b (ceilLog2 o.mainRows) q.index = false := by
  unfold reqMessageLayoutOk at h
  have hne : inIt.isEmpty = false := by
    cases inIt with
    | nil => cases hA
    | cons _ _ => rfl
  rw [hne, Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i c pad hc hp
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, laidOk, laidMatrixOk,
      List.mem_flatMap, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hm, -⟩, hall⟩ := h
    obtain ⟨hr, hq⟩ := hall b ⟨A, hA, hb⟩
    obtain ⟨hi, hce⟩ := Array.getElem?_eq_some_iff.1 hc
    have e : codes.base.getD o.code default = c := by
      simp [Array.getD_eq_getD_getElem?, hc]
    refine ⟨pad, hi, hp, ?_, hr, ?_⟩
    · rw [e]
      exact ((hm A hA).1.1 b hb).1.1
    · intro q hqm hmain
      rcases hq q hqm with k | k
      · exact absurd hmain k
      · exact k
  · cases h

/-! ## The geometry -/

/-- **THE GEOMETRY, IN THE PROGRAMS' OWN LETTERS.** Under the test on a layout, wherever an array
of link l holds an element, the message that the array names is there in the request's shape, its
sample has a pad, and the element's seat lies below the message's main rows, below 2 ^ logEll of
its main code, and at no main place of that pad. -/
theorem laidAt_geometry {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (h : reqLayoutOk codes shape layout = true) {l : Nat} {as : List ReqArray}
    (hl : layout.link[l]? = some as) {A : ReqArray} (hA : A ∈ as) {i c r p : Nat}
    (hat : laidAt A i c = some (r, p)) :
    ∃ m pad, messageAt shape l A.message = some m ∧ Send.pad codes m.shape = some pad ∧
      m.shape.code < codes.base.size ∧ r < m.shape.mainRows ∧
      p < 2 ^ (codes.base.getD m.shape.code default).logEll ∧
      ∀ q ∈ pad, q.part = .main → q.index ≠ r + p * 2 ^ ceilLog2 m.shape.mainRows := by
  obtain ⟨m, hm, hM⟩ := message_of_layout h hl hA
  obtain ⟨b, hb, hin⟩ := laidAt_block hat
  have hA' : A ∈ as.filter fun a => a.message == A.message :=
    List.mem_filter.2 ⟨hA, beq_self_eq_true _⟩
  obtain ⟨pad, hc, hp, hok, hrow, hoff⟩ := block_of_message hM hA' hb
  simp only [laidBlockOk, laidAligned, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨k1, -⟩, k3⟩, -⟩, -⟩, -⟩, k7⟩, -⟩, k9⟩ := hok
  have R := laidIn_rect k1 hin
  have hr : r < m.shape.mainRows := Nat.lt_of_lt_of_le R.2.1 hrow
  refine ⟨m, pad, hm, hp, hc, hr, Nat.lt_of_lt_of_le R.2.2.2 (aligned_inside k3 k7.2 k9), ?_⟩
  intro q hq hmain e
  have t := covers_of_rect (Nat.lt_of_lt_of_le hr (le_pow_ceil _)) R
  rw [← e, hoff q hq hmain] at t
  cases t

/-! ## The pad as the witness's accessor reads it -/

/-- **A place that padB takes for a pad's main place, inside the row, is a main place of the
sample's pad**, as soon as the message has an answer. (padB says of itself: at one answer. The
sample's pad has as many places for EACH answer; padB's are those of the last answer.) -/
theorem pad_of_padB {codes : Codes} {s : OracleShape} {pad : List PadPlace} {r p : Nat}
    (hp : Send.pad codes s = some pad) (ha : 1 ≤ s.answers)
    (hB : padB codes s false r p = true) (hlt : p < (codes.base.getD s.code default).ell) :
    ∃ q ∈ pad, q.part = .main ∧ q.index = r + p * 2 ^ ceilLog2 s.mainRows := by
  unfold padB at hB
  simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
  obtain ⟨⟨hz, hr⟩, hle⟩ := hB
  have hm : 0 < s.mainRows := by omega
  unfold Send.pad Send.cube at hp
  simp only [hz, hm, Nat.lt_irrefl, decide_false, decide_true, Bool.false_or, Bool.false_eq_true,
    if_false, if_true] at hp
  by_cases h3 : s.mainDeg = 3
  · simp only [h3, beq_self_eq_true, if_true, Nat.one_mul] at hp hle
    split at hp
    · cases hp
    · have e := Option.some.inj hp
      subst e
      refine ⟨_, List.mem_flatMap.2 ⟨s.answers - 1, List.mem_range.2 (by omega),
        List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩⟩, rfl, ?_⟩
      show s.mainRows - 1 + ((codes.base.getD s.code default).ell - s.answers +
        (s.answers - 1) + 0) * 2 ^ ceilLog2 s.mainRows = r + p * 2 ^ ceilLog2 s.mainRows
      have e1 : (codes.base.getD s.code default).ell - s.answers + (s.answers - 1) + 0 = p := by
        omega
      rw [e1]
      omega
  · have h3' : (s.mainDeg == 3) = false := by simpa using h3
    simp only [h3, h3', Bool.false_eq_true, if_false] at hp hle
    split at hp
    · cases hp
    · have e := Option.some.inj hp
      subst e
      refine ⟨_, List.mem_flatMap.2 ⟨s.answers - 1, List.mem_range.2 (by omega),
        List.mem_map.2 ⟨p + 3 - (codes.base.getD s.code default).ell,
          List.mem_range.2 (by omega), rfl⟩⟩, rfl, ?_⟩
      show s.mainRows - 1 + ((codes.base.getD s.code default).ell - 3 * s.answers +
        3 * (s.answers - 1) + (p + 3 - (codes.base.getD s.code default).ell)) *
          2 ^ ceilLog2 s.mainRows = r + p * 2 ^ ceilLog2 s.mainRows
      have e1 : (codes.base.getD s.code default).ell - 3 * s.answers + 3 * (s.answers - 1) +
          (p + 3 - (codes.base.getD s.code default).ell) = p := by
        omega
      rw [e1]
      omega

/-- **And back, at one answer**: every main place of the sample's pad is one that padB takes for a
pad's main place, in the last main row and inside the row. -/
theorem padB_of_pad {codes : Codes} {s : OracleShape} {pad : List PadPlace}
    (hp : Send.pad codes s = some pad) (ha : s.answers = 1) (hm : 0 < s.mainRows)
    {q : PadPlace} (hq : q ∈ pad) (hmain : q.part = .main) :
    ∃ p, q.index = (s.mainRows - 1) + p * 2 ^ ceilLog2 s.mainRows ∧
      p < (codes.base.getD s.code default).ell ∧ padB codes s false (s.mainRows - 1) p = true := by
  unfold Send.pad Send.cube at hp
  by_cases hz : s.maskRows = 0
  · have hrow : s.mainRows - 1 + 1 = s.mainRows := by omega
    simp only [hz, hm, ha, Nat.lt_irrefl, decide_false, decide_true, Bool.false_or,
      Bool.false_eq_true, if_false, if_true, Nat.mul_one] at hp
    by_cases h3 : s.mainDeg = 3
    · simp only [h3, beq_self_eq_true, if_true] at hp
      split at hp
      · cases hp
      · have e := Option.some.inj hp
        subst e
        obtain ⟨i, hi, hq'⟩ := List.mem_flatMap.1 hq
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq'
        have hi' := List.mem_range.1 hi
        have ht' := List.mem_range.1 ht
        refine ⟨_, rfl, by omega, ?_⟩
        unfold padB
        simp only [Bool.false_eq_true, if_false, hz, hrow, h3, beq_self_eq_true, if_true,
          Bool.true_and, decide_eq_true_eq]
        omega
    · have h3' : (s.mainDeg == 3) = false := by simpa using h3
      simp only [h3', Bool.false_eq_true, if_false] at hp
      split at hp
      · cases hp
      · have e := Option.some.inj hp
        subst e
        obtain ⟨i, hi, hq'⟩ := List.mem_flatMap.1 hq
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq'
        have hi' := List.mem_range.1 hi
        have ht' := List.mem_range.1 ht
        refine ⟨_, rfl, by omega, ?_⟩
        unfold padB
        simp only [Bool.false_eq_true, if_false, hz, hrow, h3, beq_self_eq_true,
          Bool.true_and, decide_eq_true_eq]
        omega
  · have hz' : 0 < s.maskRows := Nat.pos_of_ne_zero hz
    simp only [hz', decide_true, Bool.true_or, if_true] at hp
    split at hp
    · cases hp
    · have e := Option.some.inj hp
      subst e
      obtain ⟨i, -, hq'⟩ := List.mem_flatMap.1 hq
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hq'
      cases hmain

/-- Under the test on the codes a main code's length is 2 ^ logEll. -/
theorem ell_pow {codes : Codes} (hC : codes.lengthsOk = true) {j : Nat}
    (hj : j < codes.base.size) :
    2 ^ (codes.base.getD j default).logEll = (codes.base.getD j default).ell := by
  unfold Codes.lengthsOk at hC
  rw [Bool.and_eq_true] at hC
  have e : codes.base.getD j default = codes.base[j] := by
    simp [Array.getD_eq_getD_getElem?, hj]
  have t := Array.all_eq_true_iff_forall_mem.1 hC.1 codes.base[j] (Array.getElem_mem hj)
  simp only [powerOfTwo, Bool.and_eq_true, beq_iff_eq] at t
  rw [e]
  exact t.2

/-- Under the test on a request's shape every message of every link has an answer. -/
theorem answers_of_shape {shape : ReqShape} (hS : reqShapeOk shape = true) {l j : Nat}
    {m : ReqMessage} (hm : messageAt shape l j = some m) : 1 ≤ m.shape.answers := by
  obtain ⟨L, hL, hj⟩ := Option.bind_eq_some_iff.1 hm
  unfold reqShapeOk at hS
  simp only [Bool.and_eq_true] at hS
  have c2 : 1 ≤ shape.answers := of_decide_eq_true hS.1.1.1.1.1.1.1.2
  have c3 := List.all_eq_true.1 hS.1.1.1.1.1.1.2 (L, l) (List.mem_zipIdx_iff_getElem?.2 hL)
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at c3
  rw [(c3.2 m (List.mem_of_getElem? hj)).1.1.1]
  exact c2

/-- The test on shape and codes together holds the test on the shape. -/
theorem shapeOk_of_reqOk {codes : Codes} {shape : ReqShape} (h : reqOk codes shape = true) :
    reqShapeOk shape = true := by
  unfold reqOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- **THE GEOMETRY, AS THE WITNESS's ACCESSOR READS IT.** Under the three tests of the programs (on
the codes, on the request's shape, on the layout), wherever an array of link l holds an element, the
seat lies below the main rows of the message that the array names, below its main code's length, and
at no place that padB takes for a pad's. -/
theorem laidAt_inside {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (hC : codes.lengthsOk = true) (hS : reqShapeOk shape = true)
    (h : reqLayoutOk codes shape layout = true) {l : Nat} {as : List ReqArray}
    (hl : layout.link[l]? = some as) {A : ReqArray} (hA : A ∈ as) {i c r p : Nat}
    (hat : laidAt A i c = some (r, p)) :
    ∃ m, messageAt shape l A.message = some m ∧ r < m.shape.mainRows ∧
      p < (codes.base.getD m.shape.code default).ell ∧ padB codes m.shape false r p = false := by
  obtain ⟨m, pad, hm, hp, hc, hr, hpl, hoff⟩ := laidAt_geometry h hl hA hat
  rw [ell_pow hC hc] at hpl
  refine ⟨m, hm, hr, hpl, ?_⟩
  cases hB : padB codes m.shape false r p with
  | false => rfl
  | true =>
    obtain ⟨q, hq, hmain, e⟩ := pad_of_padB hp (answers_of_shape hS hm) hB hpl
    exact absurd e (hoff q hq hmain)

end Meaning

#print axioms Meaning.number_lt
#print axioms Meaning.aligned_inside
#print axioms Meaning.le_pow_ceil
#print axioms Meaning.laidIn_rect
#print axioms Meaning.covers_of_rect
#print axioms Meaning.laidAt_block
#print axioms Meaning.message_of_layout
#print axioms Meaning.block_of_message
#print axioms Meaning.laidAt_geometry
#print axioms Meaning.pad_of_padB
#print axioms Meaning.padB_of_pad
#print axioms Meaning.ell_pow
#print axioms Meaning.answers_of_shape
#print axioms Meaning.shapeOk_of_reqOk
#print axioms Meaning.laidAt_inside
