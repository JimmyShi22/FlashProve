-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ItemsBackMore.lean: reading undoes spelling, for four parameter items of a proof
file's first chain: "pending rows", "links' identifiers", "layout" and "request's shape". General in
the value, under the value's test with code (Johnson/AtFull/Made/ItemTests.lean).

The frame, and the same laws for the items that a key file's chains have too, are in
Johnson/HB/LLHARD/KB9/Spells.lean and ItemsBack.lean. As there, each reader
(OnBytes/Params/Items.lean) is a `do` block, `spells_bind` carries the sentence "this reader reads
this value off this string, wherever the string stands" along the block, and the speller's text
(OnBytes/Params/Spell.lean) is brought to the same row of appends by rewriting.

The reader of a chain of links first reads plain numbers and builds its value from them at the end.
So the numbers get a speller and a test of their own here (`spellSix`, `sixB`, `spellLinkWords`,
`linkWordsB`). Under the value's test the value's spelling is the spelling of its numbers
(`spell_message`, `links_spell`), and what the reader builds from the numbers is the value
(`message_back`, `links_back`, `last_back`).

  `spells_words`, `spells_block`, `spells_name`, `spells_array`, `spells_arrays`, `spells_layout`,
    `spells_six`, `spells_linkWords`, `spells_req`: the reader reads the value off its spelling,
    wherever that stands, where the value's test accepts.
  **`readWord_spell`, `readWords_spell`, `readLayout_spell`, `readReq_spell`**: so the item's reader
    on the whole item returns the value.

Limits. One direction: nothing on a string that is no spelling. Nothing where a test rejects.
Nothing on soundness.
-/
import Johnson.AtFull.Made.ItemTests
import Johnson.HB.LLHARD.KB9.ItemsBack
import Fmt.ParamsReadLawsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.KB9

/-! ## Lengths of at least a byte, and a list spelled through a function -/

theorem size_word (n : Nat) : 1 ≤ (spellWord n).size := by
  unfold spellWord
  rw [Fmt.size_u64n]
  omega

theorem one_le_size_list {α : Type} (sp : α → ByteArray) (l : List α) :
    1 ≤ (Fmt.list sp l).size := by
  unfold Fmt.list
  rw [ByteArray.size_append, Fmt.size_u64n]
  omega

/-- If each member x of a list has the spelling of f x, the list has the spelling of its image
under f. -/
theorem list_map {α β : Type} (sp : α → ByteArray) (sq : β → ByteArray) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, sp x = sq (f x)) : Fmt.list sp l = Fmt.list sq (l.map f) := by
  have e : l.map sp = l.map (sq ∘ f) := List.map_congr_left h
  unfold Fmt.list
  rw [List.length_map, List.map_map, e]

/-! ## "pending rows" and "links' identifiers" -/

theorem readWord_spell {n : Nat} (h : wB n = true) : readWord (spellWord n) = some n :=
  whole_of_spells (spells_word (w_of h))

theorem spells_words {l : List Nat} (h : wordsB l = true) :
    Spells (listOf word) (spellWords l) l := by
  simp only [wordsB, Bool.and_eq_true, List.all_eq_true] at h
  exact spells_list (ok := fun x => wB x = true) (fun _ hx => spells_word (w_of hx))
    (fun x _ => size_word x) (w_of h.1) h.2

theorem readWords_spell {l : List Nat} (h : wordsB l = true) :
    readWords (spellWords l) = some l :=
  whole_of_spells (spells_words h)

/-! ## "layout" -/

theorem spells_block {b : LaidBlock} (h : blockB b = true) :
    Spells laidBlock (spellBlock b) b := by
  simp only [blockB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine Spells.cast (y := b)
    (spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_bind (spells_word (w_of h5))
    (spells_bind (spells_word (w_of h6))
    (spells_bind (spells_word (w_of h7))
    (spells_bind (spells_word (w_of h8))
    (spells_bind (spells_flag b.iIsLow)
    (spells_pure _)))))))))) ?_
  unfold spellBlock
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem size_block (b : LaidBlock) : 1 ≤ (spellBlock b).size := by
  unfold spellBlock
  rw [ByteArray.size_append]
  have := size_row b.firstI
    [b.firstC, b.firstRow, b.firstPlace, b.bitsI, b.bitsC, b.rowBits, b.placeBits]
  omega

/-- A name within the format's rule, shorter than 2 ^ 64 bytes: its bytes are read off its
spelling. -/
theorem spells_name {s : String} (h : Fmt.nameFit s = true) :
    Spells (cut Fmt.rdName) (Fmt.textS s) (Fmt.ascii s) := by
  simp only [Fmt.nameFit, Bool.and_eq_true, decide_eq_true_eq] at h
  exact fun pre post => Fmt.undoes_name (Fmt.ascii s) ⟨h.2, Fmt.isName_ascii s h.1⟩ pre post

theorem spells_array {a : ReqArray} (h : arrayB a = true) : Spells reqArray (spellArray a) a := by
  simp only [arrayB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hn : Fmt.okName a.name = true := by
    simp only [Fmt.nameFit, Bool.and_eq_true] at h1
    exact h1.1
  have B : Spells (listOf laidBlock) (Fmt.list spellBlock a.blocks) a.blocks :=
    spells_list (ok := fun x => blockB x = true) (fun _ hx => spells_block hx)
      (fun x _ => size_block x) (w_of h5) h6
  have k : Spells reqArray
      (Fmt.textS a.name ++ (spellWord a.message ++ (spellWord a.sizeI ++ (spellWord a.sizeC ++
        (Fmt.list spellBlock a.blocks ++ ByteArray.empty)))))
      ⟨Fmt.nameOf (Fmt.ascii a.name), a.message, a.sizeI, a.sizeC, a.blocks⟩ :=
    spells_bind (spells_name h1)
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_bind B
    (spells_pure _)))))
  rw [Fmt.nameOf_ascii a.name hn] at k
  refine Spells.cast (y := a) k ?_
  unfold spellArray
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem size_array (a : ReqArray) : 1 ≤ (spellArray a).size := by
  unfold spellArray
  rw [ByteArray.size_append, ByteArray.size_append]
  have := size_row a.message [a.sizeI, a.sizeC]
  omega

theorem spells_arrays {l : List ReqArray} (h : arraysB l = true) :
    Spells (listOf reqArray) (Fmt.list spellArray l) l := by
  simp only [arraysB, Bool.and_eq_true, List.all_eq_true] at h
  exact spells_list (ok := fun x => arrayB x = true) (fun _ hx => spells_array hx)
    (fun x _ => size_array x) (w_of h.1) h.2

theorem spells_layout {y : ReqLayout} (h : layoutB y = true) :
    Spells reqLayout (spellLayout y) y := by
  simp only [layoutB, Bool.and_eq_true, List.all_eq_true] at h
  have L : Spells (listOf (listOf reqArray)) (Fmt.list (Fmt.list spellArray) y.link) y.link :=
    spells_list (ok := fun x => arraysB x = true) (fun _ hx => spells_arrays hx)
      (fun x _ => one_le_size_list _ x) (w_of h.1) h.2
  refine Spells.cast (y := y) (spells_bind L (spells_pure _)) ?_
  unfold spellLayout
  simp only [ByteArray.append_empty]

theorem readLayout_spell {y : ReqLayout} (h : layoutB y = true) :
    readLayout (spellLayout y) = some y :=
  whole_of_spells (spells_layout h)

/-! ## "request's shape": the numbers that the reader reads -/

/-- The six numbers of an oracle message of a link. -/
abbrev Six : Type := Nat × Nat × Nat × Nat × Nat × Nat

/-- Six numbers as six words. -/
def spellSix (x : Six) : ByteArray :=
  spellRow [x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2]

/-- Six numbers below 2 ^ 64 that meet the reader's demand on the degree. -/
def sixB (x : Six) : Bool :=
  wB x.1 && wB x.2.1 && wB x.2.2.1 && wB x.2.2.2.1 && wB x.2.2.2.2.1 && wB x.2.2.2.2.2 &&
    (x.2.1 == 1 || x.2.1 == 3) && (x.1 != 0 || x.2.1 == 1)

theorem spells_six {x : Six} (h : sixB x = true) : Spells reqWords (spellSix x) x := by
  simp only [sixB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, d1⟩, d2⟩ := h
  have dm : ((x.2.1 == 1 || x.2.1 == 3) && (x.1 != 0 || x.2.1 == 1)) = true := by
    rw [d1, d2]
    rfl
  refine Spells.cast (y := x)
    (spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_bind (spells_word (w_of h5))
    (spells_bind (spells_word (w_of h6))
    (spells_bind (spells_demand dm)
    (spells_pure _)))))))) ?_
  unfold spellSix
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

/-- The numbers of one link: its number of plain scalars, and its messages' numbers. -/
def spellLinkWords (x : Nat × List Six) : ByteArray := spellWord x.1 ++ Fmt.list spellSix x.2

def linkWordsB (x : Nat × List Six) : Bool := wB x.1 && wB x.2.length && x.2.all sixB

/-- The reader of one link's numbers: the text that stands inside `reqShape`. -/
def linkWords : Cut (Nat × List Six) := do
  let p ← word
  let m ← listOf reqWords
  pure (p, m)

theorem spells_linkWords {x : Nat × List Six} (h : linkWordsB x = true) :
    Spells linkWords (spellLinkWords x) x := by
  simp only [linkWordsB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have M : Spells (listOf reqWords) (Fmt.list spellSix x.2) x.2 :=
    spells_list (ok := fun y => sixB y = true) (fun _ hy => spells_six hy)
      (fun y _ => size_row _ _) (w_of h2) h3
  refine Spells.cast (y := x) (spells_bind (spells_word (w_of h1)) (spells_bind M
    (spells_pure _))) ?_
  unfold spellLinkWords
  simp only [ByteArray.append_empty]

theorem size_linkWords (x : Nat × List Six) : 1 ≤ (spellLinkWords x).size := by
  unfold spellLinkWords
  rw [ByteArray.size_append]
  have := size_word x.1
  omega

theorem size_notice (n : OracleNotice) : 1 ≤ (spellNotice n).size := by
  unfold spellNotice
  rw [ByteArray.size_append]
  have := size_word n.leafClass
  omega

/-! ## "request's shape": from the value to its numbers and back -/

theorem six_of_message {c z a : Nat} {m : ReqMessage} (h : messageB c z a m = true) :
    sixB (wordsOf m) = true := by
  simp only [messageB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, d1⟩, d2⟩, _⟩, _⟩, _⟩ := h
  simp only [sixB, wordsOf, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, d1⟩, d2⟩

/-- Under its test a message's spelling is the spelling of its six numbers. -/
theorem spell_message {c z a : Nat} {m : ReqMessage} (h : messageB c z a m = true) :
    spellReqMessage m = spellSix (wordsOf m) := by
  simp only [messageB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, d2⟩, _⟩, _⟩, _⟩ := h
  have e : (if m.shape.mainRows != 0 then m.shape.mainDeg else 1) = m.shape.mainDeg := by
    by_cases hr : (m.shape.mainRows != 0) = true
    · rw [if_pos hr]
    · rw [if_neg hr]
      simp only [hr, Bool.false_or, beq_iff_eq] at d2
      exact d2.symm
  unfold spellReqMessage spellSix wordsOf
  rw [e]

/-- Under its test a message is what the reader builds from its six numbers. -/
theorem message_back {c z a : Nat} {m : ReqMessage} (h : messageB c z a m = true) :
    reqMessage c z a (wordsOf m) = m := by
  simp only [messageB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, e1⟩, e2⟩, e3⟩ := h
  have e1 := eq_of_beq e1
  have e2 := eq_of_beq e2
  have e3 := eq_of_beq e3
  show (⟨⟨if m.shape.mainRows == 0 then noId else c, m.shape.mainRows, m.shape.mainDeg,
    m.shape.maskRows, if m.shape.maskRows == 0 then noId else z, a⟩, m.leafClass, m.moment,
    m.life⟩ : ReqMessage) = m
  rw [← e1, ← e2, ← e3]

theorem linkWords_of_link {c z a : Nat} {l : ReqLink} (h : reqLinkB c z a l = true) :
    linkWordsB (l.plain, l.messages.map wordsOf) = true := by
  simp only [reqLinkB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [linkWordsB, Bool.and_eq_true, List.all_eq_true, List.length_map]
  refine ⟨⟨h1, h2⟩, fun y hy => ?_⟩
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hy
  exact six_of_message (h3 m hm)

theorem spell_link {c z a : Nat} {l : ReqLink} (h : reqLinkB c z a l = true) :
    spellReqLink l = spellLinkWords (l.plain, l.messages.map wordsOf) := by
  simp only [reqLinkB, Bool.and_eq_true, List.all_eq_true] at h
  unfold spellReqLink spellLinkWords
  rw [list_map spellReqMessage spellSix wordsOf l.messages fun m hm => spell_message (h.2 m hm)]

theorem link_back {c z a : Nat} {l : ReqLink} (h : reqLinkB c z a l = true) :
    (⟨l.plain, (l.messages.map wordsOf).map (reqMessage c z a)⟩ : ReqLink) = l := by
  simp only [reqLinkB, Bool.and_eq_true, List.all_eq_true] at h
  have e : (l.messages.map wordsOf).map (reqMessage c z a) = l.messages := by
    rw [List.map_map]
    have t : ∀ m ∈ l.messages, (reqMessage c z a ∘ wordsOf) m = id m :=
      fun m hm => message_back (h.2 m hm)
    rw [List.map_congr_left t, List.map_id]
  rw [e]

/-- Under the links' tests the links' spelling is the spelling of their numbers. -/
theorem links_spell {s : ReqShape}
    (h : ∀ l ∈ s.link, reqLinkB s.code s.maskCode s.answers l = true) :
    Fmt.list spellReqLink s.link = Fmt.list spellLinkWords (linksWords s) :=
  list_map spellReqLink spellLinkWords (fun l => (l.plain, l.messages.map wordsOf)) s.link
    fun l hl => spell_link (h l hl)

/-- Under the links' tests the links are what the reader builds from their numbers. -/
theorem links_back {s : ReqShape}
    (h : ∀ l ∈ s.link, reqLinkB s.code s.maskCode s.answers l = true) :
    ((linksWords s).map fun l =>
      (⟨l.1, l.2.map (reqMessage s.code s.maskCode s.answers)⟩ : ReqLink)) = s.link := by
  unfold linksWords
  rw [List.map_map]
  have t : ∀ l ∈ s.link, ((fun l : Nat × List Six =>
      (⟨l.1, l.2.map (reqMessage s.code s.maskCode s.answers)⟩ : ReqLink)) ∘
      fun l : ReqLink => (l.plain, l.messages.map wordsOf)) l = id l :=
    fun l hl => link_back (h l hl)
  rw [List.map_congr_left t, List.map_id]

/-- A list that begins with x is x in front of the list without its first member. -/
theorem last_back {l : List IoppStage} {x : IoppStage} (h : l.head? = some x) :
    x :: l.drop 1 = l := by
  cases l with
  | nil => cases h
  | cons a t =>
    cases h
    rfl

/-! ## "request's shape" -/

theorem spells_req {s : ReqShape} (h : reqB s = true) : Spells reqShape (spellReq s) s := by
  simp only [reqB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, hk⟩ := h
  have hl : (linksWords s).length < 2 ^ 64 := by
    unfold linksWords
    rw [List.length_map]
    exact w_of h3
  have ha : ∀ x ∈ linksWords s, linkWordsB x = true := by
    intro x hx
    obtain ⟨l, hm, rfl⟩ := List.mem_map.1 hx
    exact linkWords_of_link (h4 l hm)
  have LW : Spells (listOf linkWords) (Fmt.list spellLinkWords (linksWords s)) (linksWords s) :=
    spells_list (ok := fun x => linkWordsB x = true) (fun _ hx => spells_linkWords hx)
      (fun x _ => size_linkWords x) hl ha
  have N : Spells (listOf notice) (Fmt.list spellNotice s.atStart) s.atStart :=
    spells_list (ok := fun x => noticeB x = true) (fun _ hx => spells_notice hx)
      (fun x _ => size_notice x) (w_of h5) h6
  have k : Spells reqShape
      (spellWord s.code ++ (spellWord s.maskCode ++ (Fmt.list spellLinkWords (linksWords s) ++
        (Fmt.list spellNotice s.atStart ++ (spellWord s.answers ++ (spellStages (s.last.drop 1) ++
        (spellChoice s.choice ++ (ByteArray.empty ++ ByteArray.empty))))))))
      { code := s.code, maskCode := s.maskCode, atStart := s.atStart, answers := s.answers,
        choice := s.choice,
        link := (linksWords s).map fun l =>
          ⟨l.1, l.2.map (reqMessage s.code s.maskCode s.answers)⟩,
        last := ⟨s.code, s.maskCode, 1, 0⟩ :: s.last.drop 1 } :=
    spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind LW
    (spells_bind N
    (spells_bind (spells_word (w_of h7))
    (spells_bind (spells_stages h9)
    (spells_bind (spells_choice s.choice)
    (spells_bind (spells_demand hk)
    (spells_pure _))))))))
  rw [links_back h4, last_back (eq_of_beq h8)] at k
  refine Spells.cast (y := s) k ?_
  unfold spellReq
  rw [links_spell h4]
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem readReq_spell {s : ReqShape} (h : reqB s = true) : readReq (spellReq s) = some s :=
  whole_of_spells (spells_req h)

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.size_word
#print axioms Johnson.AtFull.Made.one_le_size_list
#print axioms Johnson.AtFull.Made.list_map
#print axioms Johnson.AtFull.Made.readWord_spell
#print axioms Johnson.AtFull.Made.spells_words
#print axioms Johnson.AtFull.Made.readWords_spell
#print axioms Johnson.AtFull.Made.spells_block
#print axioms Johnson.AtFull.Made.size_block
#print axioms Johnson.AtFull.Made.spells_name
#print axioms Johnson.AtFull.Made.spells_array
#print axioms Johnson.AtFull.Made.size_array
#print axioms Johnson.AtFull.Made.spells_arrays
#print axioms Johnson.AtFull.Made.spells_layout
#print axioms Johnson.AtFull.Made.readLayout_spell
#print axioms Johnson.AtFull.Made.spells_six
#print axioms Johnson.AtFull.Made.spells_linkWords
#print axioms Johnson.AtFull.Made.size_linkWords
#print axioms Johnson.AtFull.Made.size_notice
#print axioms Johnson.AtFull.Made.six_of_message
#print axioms Johnson.AtFull.Made.spell_message
#print axioms Johnson.AtFull.Made.message_back
#print axioms Johnson.AtFull.Made.linkWords_of_link
#print axioms Johnson.AtFull.Made.spell_link
#print axioms Johnson.AtFull.Made.link_back
#print axioms Johnson.AtFull.Made.links_spell
#print axioms Johnson.AtFull.Made.links_back
#print axioms Johnson.AtFull.Made.last_back
#print axioms Johnson.AtFull.Made.spells_req
#print axioms Johnson.AtFull.Made.readReq_spell
