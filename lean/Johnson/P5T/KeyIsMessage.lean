-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/KeyIsMessage.lean: THE KEY (0, l, k) OF A SEAT OFF THE LIST OF ROUNDS AND THE NUMBER BY
WHICH A REQUEST's ARRAY NAMES ITS MESSAGE ARE PLACES IN ONE LIST: the messages of link l of the
request's shape. Definitions with code, statements and proofs. On public data alone.
  `msgAt S l k`: message k of link l of the shape S.
  (BY THE MAKE, no test: a seat of `planSeats` with the role "own k" in the sending "link l, moment
    m" names message k of link l, of that moment: `planSeats_own`, Johnson/P5T/PlanFacts.lean: not
    typed anew here, and not called.)
  `array_is_place`: where the programs' own test on a layout (`reqLayoutOk`) accepts, every array A
    of link l names a message of link l: `msgAt S l A.message` is there, and the arrays of link l
    that name it are laid within ITS shape (`reqMessageLayoutOk`).
  `key_is_place`: where `rolesFit` finds no fault: every seat with the key (0, l, k), the original
    and every kept copy alike, names message k of link l, with that message's code, main rows and
    degree.
  `coverB layout ps`: A TEST WITH CODE: every array A of every link l of the layout has a seat with
    the key (0, l, A.message) whose tree and tenant are first held by a seat of that key.
    `cover_gives`: then `arrOf` at that seat's tree and tenant is `numOfPlan ps l A.message`, and
    that is the place of a key that is there, not "the number of keys".
  `l4`: under the three tests: whatever `seatIn layout (numOfPlan ps)` answers at an array A of link
    l has as its first component `arrOf` at the tree and tenant of a seat p with the key
    (0, l, A.message); p has the code, main rows and degree of the very message x that A names; and
    the arrays that name x are laid within x's shape.
  `coverB_empty`, `coverB_past`: negative tests: it rejects where no seat is listed, and where the
    one listed key is another message's.
NOT HERE. That `coverB`, `rolesFit` and `reqLayoutOk` accept at any public data. That the verifier's
own reader of a message's number (`ReqFrame.whereIs`: own[k]) finds message k of that list: a fact
on the verifier's state. Nothing on soundness.

-/
import Johnson.P5T.NumOfPlan
import OnBytes.Iop.ReqRows
import Johnson.Desc.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes OnBytes.Params
open VerifiableInference.Desc (seatIn arrayOf laidAt)

/-- Message k of link l. -/
def msgAt (S : ReqShape) (l k : Nat) : Option ReqMessage := (S.link[l]?).bind (·.messages[k]?)

/-- **An array's number is a place in its link's list of messages.** -/
theorem array_is_place {codes : Codes} {S : ReqShape} {layout : ReqLayout}
    (h : reqLayoutOk codes S layout = true) {l : Nat} {As : List ReqArray}
    (hl : layout.link[l]? = some As) {A : ReqArray} (hA : A ∈ As) :
    ∃ x, msgAt S l A.message = some x ∧
      reqMessageLayoutOk codes x.shape (As.filter fun a => a.message == A.message) = true := by
  unfold reqLayoutOk at h
  rw [Bool.and_eq_true, beq_iff_eq, zipT_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  have hlt : l < layout.link.length := (List.getElem?_eq_some_iff.1 hl).1
  have hlt' : l < S.link.length := by omega
  have hz : (S.link[l], As) ∈ S.link.zip layout.link := by
    refine List.mem_iff_getElem?.2 ⟨l, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨List.getElem?_eq_getElem hlt', hl⟩
  have h1 := hall _ hz
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h1
  have h2 : A.message < (S.link[l]).messages.length := h1.1.1.2 A hA
  refine ⟨(S.link[l]).messages[A.message], ?_, ?_⟩
  · unfold msgAt
    rw [List.getElem?_eq_getElem hlt']
    exact List.getElem?_eq_getElem h2
  · refine h1.2 ((S.link[l]).messages[A.message], A.message) ?_
    refine List.mem_iff_getElem?.2 ⟨A.message, ?_⟩
    rw [List.getElem?_zipIdx, List.getElem?_eq_getElem h2]
    simp

/-- A seat of a sending that is no link's has no role. -/
theorem role_of_noSeg {Z : ProofFile.Pub} {dl : List Fmt.DeclaredRound} {p : PSeat}
    (h : p ∈ planSeats Z dl) (hs : p.seg = none) : p.role = .other := by
  unfold planSeats at h
  simp only [List.mem_flatMap] at h
  obtain ⟨s, _, h⟩ := h
  split at h
  · cases h
  · obtain ⟨i, _, rfl⟩ := List.mem_map.1 h
    dsimp only at hs ⊢
    rw [hs]
    rfl

/-- **A key (0, l, k) names message k of link l**, at the original and at every kept copy. -/
theorem key_is_place {Z : ProofFile.Pub} {dl : List Fmt.DeclaredRound}
    (hf : rolesFit Z (planSeats Z dl) = []) {p : PSeat} (hp : p ∈ planSeats Z dl) {l k : Nat}
    (hk : keyOf p = (0, l, k)) :
    ∃ x, msgAt Z.first.shape l k = some x ∧
      (x.shape.code, x.shape.mainRows, x.shape.mainDeg) =
        (p.shape.code, p.shape.mainRows, p.shape.mainDeg) := by
  unfold rolesFit at hf
  have h1 := List.filterMap_eq_nil_iff.1 hf p hp
  have h0 := role_of_noSeg hp
  unfold keyOf at hk
  unfold msgAt
  rcases hs : p.seg with _ | ⟨l', m⟩
  · rw [h0 hs] at hk
    simp [hs] at hk
  · rw [hs] at h1 hk
    rcases hr : p.role with _ | ⟨l₀, k₀⟩ | k₀ | _ | i | _ <;> rw [hr] at h1 hk <;>
      simp only [Prod.mk.injEq, one_ne_zero, false_and] at hk
    · obtain ⟨_, rfl, rfl⟩ := hk
      simp only [ite_eq_left_iff, reduceCtorEq, imp_false, not_not, beq_iff_eq] at h1
      obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h1
      exact ⟨x, hx, e⟩
    · obtain ⟨_, rfl, rfl⟩ := hk
      simp only [ite_eq_left_iff, reduceCtorEq, imp_false, not_not, beq_iff_eq] at h1
      obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h1
      exact ⟨x, hx, by rw [e]⟩

/-- **The test**: every array of every link has a seat with its key, whose tree and tenant are first
held by a seat of that key. -/
def coverB (layout : ReqLayout) (ps : List PSeat) : Bool :=
  layout.link.zipIdx.all fun x => x.1.all fun A => ps.any fun p =>
    keyOf p == (0, x.2, A.message) &&
      (ps.find? fun q => q.j == p.j && q.t == p.t).map keyOf == some (0, x.2, A.message)

/-- What the test gives. -/
theorem cover_gives {layout : ReqLayout} {ps : List PSeat} (h : coverB layout ps = true) {l : Nat}
    {As : List ReqArray} (hl : layout.link[l]? = some As) {A : ReqArray} (hA : A ∈ As) :
    ∃ p ∈ ps, keyOf p = (0, l, A.message) ∧ arrOf ps p.j p.t = numOfPlan ps l A.message ∧
      numOfPlan ps l A.message < ((ps.map keyOf).eraseDups).length := by
  unfold coverB at h
  rw [List.all_eq_true] at h
  have hz : (As, l) ∈ layout.link.zipIdx := by
    refine List.mem_iff_getElem?.2 ⟨l, ?_⟩
    rw [List.getElem?_zipIdx, hl]
    simp
  have h1 := List.all_eq_true.1 (h _ hz) A hA
  obtain ⟨p, hp, h2⟩ := List.any_eq_true.1 h1
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h2
  obtain ⟨p₀, hp₀, hk₀⟩ := Option.map_eq_some_iff.1 h2.2
  refine ⟨p, hp, h2.1, arrOf_is_num ps p.j p.t l A.message p₀ hp₀ hk₀, ?_⟩
  unfold numOfPlan
  refine List.idxOf_lt_length_iff.2 ?_
  rw [List.mem_eraseDups]
  exact List.mem_map.2 ⟨p, hp, h2.1⟩

/-- **(L4).** -/
theorem l4 {Z : ProofFile.Pub} {dl : List Fmt.DeclaredRound} {codes : Codes} {layout : ReqLayout}
    (hLay : reqLayoutOk codes Z.first.shape layout = true)
    (hFit : rolesFit Z (planSeats Z dl) = []) (hCov : coverB layout (planSeats Z dl) = true)
    {l : Nat} {name : String} {i c : Nat} {y : Nat × Nat × Nat}
    (hy : seatIn layout (numOfPlan (planSeats Z dl)) l name i c = some y) :
    ∃ A As x p, arrayOf layout l name = some A ∧ layout.link[l]? = some As ∧ A ∈ As ∧
      msgAt Z.first.shape l A.message = some x ∧
      reqMessageLayoutOk codes x.shape (As.filter fun a => a.message == A.message) = true ∧
      p ∈ planSeats Z dl ∧ keyOf p = (0, l, A.message) ∧
      y.1 = arrOf (planSeats Z dl) p.j p.t ∧
      y.1 < (((planSeats Z dl).map keyOf).eraseDups).length ∧
      (x.shape.code, x.shape.mainRows, x.shape.mainDeg) =
        (p.shape.code, p.shape.mainRows, p.shape.mainDeg) := by
  unfold seatIn at hy
  obtain ⟨A, hA, hy⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨z, _, rfl⟩ := Option.map_eq_some_iff.1 hy
  have hA' := hA
  unfold arrayOf at hA'
  obtain ⟨As, hl, hf⟩ := Option.bind_eq_some_iff.1 hA'
  have hmem : A ∈ As := List.mem_of_find?_eq_some hf
  obtain ⟨p, hp, hk, ha, hlt⟩ := cover_gives hCov hl hmem
  obtain ⟨x, hx, hs⟩ := key_is_place hFit hp hk
  obtain ⟨x', hx', hfit⟩ := array_is_place hLay hl hmem
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  exact ⟨A, As, x, p, hA, hl, hmem, hx, hfit, hp, hk, ha.symm, hlt, hs⟩

/-- Negative test: no seat is listed, and the layout has an array. -/
theorem coverB_empty (A : ReqArray) : coverB ⟨[[A]]⟩ [] = false := rfl

/-- Negative test: the one listed seat holds another message of the link. -/
theorem coverB_past (A : ReqArray) (p : PSeat) (hs : p.seg = some (0, 0))
    (hr : p.role = .own (A.message + 1)) : coverB ⟨[[A]]⟩ [p] = false := by
  simp [coverB, keyOf, hs, hr]

end P5T

#print axioms P5T.array_is_place
#print axioms P5T.role_of_noSeg
#print axioms P5T.key_is_place
#print axioms P5T.cover_gives
#print axioms P5T.l4
#print axioms P5T.coverB_empty
#print axioms P5T.coverB_past
