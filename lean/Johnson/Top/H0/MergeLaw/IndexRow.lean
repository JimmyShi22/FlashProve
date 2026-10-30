-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/IndexRow.lean: the two readings of the index masks are one. One theorem with
its proof, two corollaries, a lemma on ranges, and a counterexample that shows why one premise is
needed.

Why. The law of the merge of the claims on the committed table reads the index masks off the witness
at one member of the list of oracle messages (`vecBy`, Pin.lean). The sentences on the pending rows
read the same entries through the verifier's state: the state names the oracle message that holds
the index masks, the state's book of trees says where that message sits, and the words of the
message are taken there (`wordsFirst`, Johnson/Desc/Sound/WordsAt.lean), cut to the size of its mask
table. MaskRow.lean shows the like equation for a segment's mask row.

Main names:
  `index_words`: THE EQUATION, at every index c. On the left: the words of the index masks' message
    at c, and 0 from the mask table's size on. On the right: `vecBy` at the member xI, at the mask
    table's size and at the positions `posMask R`, R the bits that number the table's rows.
    Premises: the seven public tests and facts on the verifier's state that `tabFirst_at_door`
    (Johnson/Desc/Sound/WordsAtDoor.lean) takes, the last of them "by the book the message sits at
    `N.index`"; the state's code table is cs; the list of shapes has xI's shape at that message;
    xI's seat is `N.index`; the number of xI's mask rows is a power of two.
  `index_words_of_test`: the same with the last premise as the library's test `powerOfTwo`.
  `index_in_msg`: the positions `posMask RI j` for j below the mask table's size lie inside xI's
    ranges (`InMsg`, Johnson/Desc/Sound/World.lean): rows below its mask rows, places below the
    length of a mask row's message. Asked beside: that length is a power of two as well.
  `index_words_of_tests`: a yes of the twelve tests with code (`indexTestsB`, IndexRowTests.lean)
    pays every premise of the two.
  `words_part_at_three`: WHY THE POWER OF TWO. The words are 0 at the idle rows of a table (from the
    number of real rows up to the next power of two); the witness's table need not be. With three
    rows and a table that is 1 everywhere, entry 3 is 0 in the first reading and 1 in the second.

Limits. No verifier's state that meets all premises is shown here. That the mask table's size is the
number of index masks that the merge's law counts is not said. Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Top.H0.MergeLaw.IndexRowTests
import Johnson.Desc.Sound.WordsAtDoor
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (Statement OracleShape ceilLog2 powerOfTwo)
open OnBytes.Slice (GE)
open OnBytes.Means (wordsOn realRows tableSize)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB
  msgShape_at)

/-- A message whose shape is sh has sh's mask rows as its real rows, and the bits that number them.
-/
theorem mask_rows_of_shape {st : Statement} {o : ℕ} {sh : OracleShape}
    (h : (st.oracles[o]?).map (·.shape) = some sh) :
    realRows st o .mask = sh.maskRows ∧ st.rowBits o .mask = ceilLog2 sh.maskRows := by
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  unfold realRows Statement.rowBits
  rw [hx]
  dsimp only
  rw [e]
  exact ⟨rfl, rfl⟩

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)

/-- **THE TWO READINGS OF THE INDEX MASKS ARE ONE, at every index**: the words of the message that
the verifier's state names as the index masks' (`wordsFirst`), cut to its mask table's size, and the
merge's reading off the witness at the member xI (`vecBy`, Pin.lean). -/
theorem index_words (N : Numbers) (M : List OracleShape) (L : Laid) (b : S) (xI : Mem) (k : ℕ)
    (h₁ : msgShapesB M b.st = true) (h₂ : bookInOrderB 0 b.book b.roots = true)
    (h₃ : seatsCarriedB L b.book = true) (hs : b.book.place.size = b.st.oracles.size)
    (hb : placesBelowB L b.book.place.size b.book.trees.size = true)
    (ht : b.out.indexMasks < b.st.oracles.size)
    (hseat : b.book.place[b.out.indexMasks]? = some N.index) (hcs : b.st.codes = cs)
    (hsh : M[b.out.indexMasks]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = N.index)
    (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k) (w : Wit Cells Tok MsgT) (c : ℕ) :
    (if c < tableSize b.st b.out.indexMasks .mask then
        wordsFirst arr b.st b.book w b.out.indexMasks .mask c else 0) =
      vecBy cs arr (tableSize b.st b.out.indexMasks .mask)
        (posMask (b.st.rowBits b.out.indexMasks .mask)) xI w c := by
  obtain ⟨sh, q, a1, a2, a3⟩ :=
    tabFirst_at_door arr M L b.st b.book b.roots h₁ h₂ h₃ hs hb w _ ht
  obtain rfl : sh = (xI.1.l.get xI.2).1 := Option.some.inj (a1.symm.trans hsh)
  obtain rfl : q = N.index := Option.some.inj (a2.symm.trans hseat)
  obtain ⟨hr, hR⟩ := mask_rows_of_shape ((msgShape_at h₁ _ ht).trans hsh)
  rw [hp] at hr
  rw [hp, OnBytes.Slice.ceilLog2_two_pow] at hR
  unfold vecBy vecOf posMask
  by_cases hc : c < tableSize b.st b.out.indexMasks .mask
  · rw [if_pos hc, if_pos hc, wordsFirst_is]
    unfold wordsOn
    rw [hr, hR, if_pos (Nat.mod_lt _ (Nat.two_pow_pos k)), a3, hcs]
    unfold memTab numOf
    have e : xI.1.seat xI.2 = N.index := hx
    rw [e]
    rfl
  · rw [if_neg hc, if_neg hc]

/-- The same, the last premise as the library's test with code. -/
theorem index_words_of_test (N : Numbers) (M : List OracleShape) (L : Laid) (b : S) (xI : Mem)
    (h₁ : msgShapesB M b.st = true) (h₂ : bookInOrderB 0 b.book b.roots = true)
    (h₃ : seatsCarriedB L b.book = true) (hs : b.book.place.size = b.st.oracles.size)
    (hb : placesBelowB L b.book.place.size b.book.trees.size = true)
    (ht : b.out.indexMasks < b.st.oracles.size)
    (hseat : b.book.place[b.out.indexMasks]? = some N.index) (hcs : b.st.codes = cs)
    (hsh : M[b.out.indexMasks]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = N.index)
    (hp : powerOfTwo (xI.1.l.get xI.2).1.maskRows = true) (w : Wit Cells Tok MsgT) (c : ℕ) :
    (if c < tableSize b.st b.out.indexMasks .mask then
        wordsFirst arr b.st b.book w b.out.indexMasks .mask c else 0) =
      vecBy cs arr (tableSize b.st b.out.indexMasks .mask)
        (posMask (b.st.rowBits b.out.indexMasks .mask)) xI w c := by
  have e : 2 ^ ceilLog2 (xI.1.l.get xI.2).1.maskRows = (xI.1.l.get xI.2).1.maskRows := by
    unfold powerOfTwo at hp
    rw [Bool.and_eq_true] at hp
    exact eq_of_beq hp.2
  exact index_words cs arr N M L b xI _ h₁ h₂ h₃ hs hb ht hseat hcs hsh hx e.symm w c

end

section
variable (cs : OnBytes.Codes)

/-- The size of the mask table of a message whose shape is sh, where sh has 2 ^ k mask rows. -/
theorem mask_size_of_shape {st : Statement} {o k : ℕ} {sh : OracleShape}
    (h : (st.oracles[o]?).map (·.shape) = some sh) (hp : sh.maskRows = 2 ^ k) :
    tableSize st o .mask = 2 ^ (k + (Johnson.Pack.pMask st.codes sh).logEll) := by
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  have hrows : x.shape.rows .mask = 2 ^ k := by rw [e]; exact hp
  have hhas : st.has o .mask = true := by
    unfold Statement.has
    rw [hx]
    dsimp only
    rw [hrows]
    exact decide_eq_true (Nat.two_pow_pos k)
  have hrow : st.rowBits o .mask = k := by
    rw [(mask_rows_of_shape h).2, hp, OnBytes.Slice.ceilLog2_two_pow]
  have hpl : st.placeBits o .mask = (Johnson.Pack.pMask st.codes sh).logEll := by
    unfold Statement.placeBits
    rw [hx]
    dsimp only
    have h0 : (x.shape.rows .mask == 0) = false := by
      rw [hrows]
      exact beq_false_of_ne (Nat.two_pow_pos k).ne'
    rw [h0, e]
    rfl
  unfold tableSize Statement.tableBits
  rw [hhas, hrow, hpl]
  rfl

/-- **THE PLACES BELOW THE MASK TABLE's SIZE LIE INSIDE THE MEMBER's RANGES.** ni: the size of the
mask table of the message o; RI: the bits that number its rows. Asked beside the shape: the number
of mask rows and the length of a mask row's message are powers of two. -/
theorem index_in_msg (M : List OracleShape) (st : Statement) (o : ℕ) (xI : Mem) (k ni RI : ℕ)
    (h₁ : msgShapesB M st = true) (ht : o < st.oracles.size) (hcs : st.codes = cs)
    (hsh : M[o]? = some (xI.1.l.get xI.2).1) (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k)
    (hl : (Johnson.Pack.pMask cs (xI.1.l.get xI.2).1).ell =
      2 ^ (Johnson.Pack.pMask cs (xI.1.l.get xI.2).1).logEll)
    (hni : tableSize st o .mask = ni) (hR : st.rowBits o .mask = RI) :
    ∀ j, j < ni → InMsg cs (xI.1.l.get xI.2).1 (posMask RI j).1 (posMask RI j).2.1
      (posMask RI j).2.2 := by
  intro j hj
  have hm := (msgShape_at h₁ _ ht).trans hsh
  have hR' : RI = k := by
    rw [← hR, (mask_rows_of_shape hm).2, hp, OnBytes.Slice.ceilLog2_two_pow]
  rw [← hni, mask_size_of_shape hm hp, hcs, pow_add] at hj
  subst hR'
  unfold InMsg posMask
  rw [if_pos rfl, hp, hl]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos RI), Nat.div_lt_of_lt_mul hj⟩

end

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)

/-- **A YES OF THE TWELVE TESTS PAYS EVERY PREMISE**: of the equation, and of the lemma on ranges.
-/
theorem index_words_of_tests (N : Numbers) (M : List OracleShape) (L : Laid) (b : S) (xI : Mem)
    (h : indexTestsB N.index M L cs (xI.1.l.get xI.2).1 (seatOf xI) b = true) :
    (∀ (w : Wit Cells Tok MsgT) (c : ℕ),
      (if c < tableSize b.st b.out.indexMasks .mask then
          wordsFirst arr b.st b.book w b.out.indexMasks .mask c else 0) =
        vecBy cs arr (tableSize b.st b.out.indexMasks .mask)
          (posMask (b.st.rowBits b.out.indexMasks .mask)) xI w c) ∧
      ∀ j, j < tableSize b.st b.out.indexMasks .mask →
        InMsg cs (xI.1.l.get xI.2).1 (posMask (b.st.rowBits b.out.indexMasks .mask) j).1
          (posMask (b.st.rowBits b.out.indexMasks .mask) j).2.1
          (posMask (b.st.rowBits b.out.indexMasks .mask) j).2.2 := by
  simp only [indexTestsB, indexTests, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h₁, h₂, h₃, hs, hb, ht, hseat, hcs, hsh, hx, hp, hl⟩ := h
  have pw : ∀ n, powerOfTwo n = true → n = 2 ^ ceilLog2 n := fun n hn => by
    unfold powerOfTwo at hn
    rw [Bool.and_eq_true] at hn
    exact (eq_of_beq hn.2).symm
  exact ⟨index_words cs arr N M L b xI _ h₁ h₂ h₃ hs hb ht hseat hcs hsh hx (pw _ hp),
    index_in_msg cs M b.st _ xI _ _ _ h₁ ht hcs hsh (pw _ hp) (pw _ hl) rfl rfl⟩

end

/-- **Why the power of two is asked.** A statement with one message of three mask rows, and the
table that is 1 everywhere: at entry 3 (row 3 of four, an idle one) the words are 0, the table is 1.
-/
theorem words_part_at_three :
    let st : Statement := { oracles := #[{ shape := { maskRows := 3 } }] }
    wordsOn st (fun _ _ _ _ => (1 : GE)) 0 .mask 3 = 0 ∧
      vecOf 4 (posMask (st.rowBits 0 .mask)) (fun _ _ _ => (1 : GE)) 3 = 1 := by
  refine ⟨?_, ?_⟩
  · unfold wordsOn
    exact if_neg (by decide)
  · unfold vecOf
    exact if_pos (by decide)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.index_words
#print axioms VerifiableInference.Desc.First.MergeLaw.index_words_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.index_in_msg
#print axioms VerifiableInference.Desc.First.MergeLaw.index_words_of_tests
#print axioms VerifiableInference.Desc.First.MergeLaw.words_part_at_three
