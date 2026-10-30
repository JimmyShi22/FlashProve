-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/ItemsBack.lean: READING UNDOES SPELLING, FOR THE FIVE PARAMETER ITEMS OF A KEY
FILE's CHAINS: the index masks' notice, the ranges, the binding tree, the codes, the test on the
table. General in the value, under the value's test with code (Johnson/HB/LLHARD/KB9/ItemsOk.lean).

Why. The library has this law for a chain's plan (`key_read_made`, OnBytes/Model/ReadBackMade.lean)
and not for the items beside it: OnBytes/Params/Spell.lean says so of itself.

How. Each reader (OnBytes/Params/Items.lean) is a `do` block over the primitives word, flag, elt and
listOf; each speller (OnBytes/Params/Spell.lean) is a row of appends over their spellings.
`spells_bind` (Johnson/HB/LLHARD/KB9/Spells.lean) carries the sentence along the block; the
speller's text is brought to the same row of appends by rewriting.

  `w_of`, `e_of`: what the two smallest tests say. `size_row`: a row of words that is not empty has
    at least a byte.
  `spells_code`, `spells_codes`, `spells_shape`, `spells_notice`, `spells_stage`, `spells_stages`,
    `spells_choice`, `spells_index`, `spells_foldeq`, `spells_lin`, `spells_binding`, `spells_run`,
    `spells_part`, `spells_lookup`, `spells_ranges`: the reader reads the value off its spelling,
    wherever that stands, where the value's test accepts.
  **`readNotice_spell`, `readRanges_spell`, `readBinding_spell`, `readCodes_spell`,
    `readLin_spell`**: so the item's reader on the whole item returns the value.

`spells_shape` is where spelling is not faithful: the speller overwrites three fields where the
shape has no rows of a kind. The test `shapeB` asks that these fields hold what is written; under it
the spelt words are the fields' own.

Limits. One direction: nothing on a string that is no spelling. Nothing where a test rejects.
Nothing on soundness.
-/
import Johnson.HB.LLHARD.KB9.Spells
import Johnson.HB.LLHARD.KB9.ItemsOk
import Fmt.Rules23Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params

theorem w_of {n : Nat} (h : wB n = true) : n < 2 ^ 64 := of_decide_eq_true h

theorem e_of {x : F} (h : eltB x = true) : x.toNat < Fmt.Fld.two.p := of_decide_eq_true h

/-- A row of words that is not empty has at least a byte. -/
theorem size_row (a : Nat) (l : List Nat) : 1 ≤ (spellRow (a :: l)).size := by
  unfold spellRow spellWord
  rw [List.map_cons, Fmt.cat_cons, ByteArray.size_append, Fmt.size_u64n]
  omega

/-! ## Codes -/

theorem spells_code {c : Code} (h : codeB c = true) : Spells code (spellCode c) c := by
  simp only [codeB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine Spells.cast
    (spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_pure _)))) ?_
  unfold spellCode
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

theorem spells_codes {c : Codes} (h : codesB c = true) : Spells codes (spellCodes c) c := by
  simp only [codesB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have L : ∀ {l : List Code}, l.length < 2 ^ 64 → (∀ x ∈ l, codeB x = true) →
      Spells (listOf code) (Fmt.list spellCode l) l := fun hl ha =>
    spells_list (ok := fun x => codeB x = true) (fun _ hx => spells_code hx)
      (fun x _ => size_row _ _) hl ha
  refine Spells.cast (y := c) (spells_bind (L (w_of h1) h2) (spells_bind (L (w_of h3) h4)
    (spells_pure _))) ?_
  unfold spellCodes
  simp only [ByteArray.append_empty]

/-! ## Shapes and notices -/

theorem spells_shape {s : OracleShape} (h : shapeB s = true) :
    Spells oracleShape (spellShape s) s := by
  simp only [shapeB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, d1⟩, d2⟩, d3⟩ := h
  have e1 : (if s.mainRows != 0 then s.code else noId) = s.code := by
    by_cases hr : (s.mainRows != 0) = true
    · rw [if_pos hr]
    · rw [if_neg hr]
      simp only [hr, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at d2
      exact d2.1.symm
  have e2 : (if s.maskRows != 0 then s.maskCode else noId) = s.maskCode := by
    by_cases hr : (s.maskRows != 0) = true
    · rw [if_pos hr]
    · rw [if_neg hr]
      simp only [hr, Bool.false_or, beq_iff_eq] at d3
      exact d3.symm
  have e3 : (if s.mainRows != 0 then s.mainDeg else 1) = s.mainDeg := by
    by_cases hr : (s.mainRows != 0) = true
    · rw [if_pos hr]
    · rw [if_neg hr]
      simp only [hr, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at d2
      exact d2.2.symm
  have dm : ((s.mainDeg == 1 || s.mainDeg == 3) && (s.mainRows != 0 || (s.code == noId &&
      s.mainDeg == 1)) && (s.maskRows != 0 || s.maskCode == noId)) = true := by
    rw [d1, d2, d3]
    rfl
  refine Spells.cast (y := s)
    (spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_bind (spells_word (w_of h5))
    (spells_bind (spells_word (w_of h6))
    (spells_bind (spells_demand dm)
    (spells_pure _)))))))) ?_
  unfold spellShape
  rw [e1, e2, e3]
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

theorem spells_notice {n : OracleNotice} (h : noticeB n = true) :
    Spells notice (spellNotice n) n := by
  simp only [noticeB, Bool.and_eq_true] at h
  refine Spells.cast (y := n)
    (spells_bind (spells_shape h.1)
    (spells_bind (spells_word (w_of h.2))
    (spells_pure _))) ?_
  unfold spellNotice
  simp only [ByteArray.append_empty]

/-! ## Stages, choices -/

theorem spells_stage {s : IoppStage} (h : stageB s = true) : Spells stage (spellStage s) s := by
  simp only [stageB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine Spells.cast
    (spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_pure _))))) ?_
  unfold spellStage
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

theorem spells_stages {l : List IoppStage} (h : stagesB l = true) :
    Spells (listOf stage) (spellStages l) l := by
  simp only [stagesB, Bool.and_eq_true, List.all_eq_true] at h
  exact spells_list (ok := fun x => stageB x = true) (fun _ hx => spells_stage hx)
    (fun x _ => size_row _ _) (w_of h.1) h.2

theorem spells_choice (c : IoppChoice) : Spells choice (spellChoice c) c := by
  refine Spells.cast (y := c) (spells_bind (spells_flag c.masksRide) (spells_pure _)) ?_
  unfold spellChoice
  simp only [ByteArray.append_empty]

/-! ## The test on the table -/

theorem spells_index {s : IndexShape} (h : indexB s = true) :
    Spells indexShape (spellIndex s) s := by
  simp only [indexB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine Spells.cast (y := s)
    (spells_bind (spells_code h1)
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_pure _))))) ?_
  unfold spellIndex
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

theorem spells_foldeq {S : FoldeqShape} (h : foldeqB S = true) :
    Spells foldeqShape (spellFoldeq S) S := by
  simp only [foldeqB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine Spells.cast (y := S)
    (spells_bind (spells_index h1)
    (spells_bind (spells_shape h2)
    (spells_bind (spells_flag S.rowsHigh)
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_pure _)))))) ?_
  unfold spellFoldeq
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem spells_lin {S : LinShape} (h : linB S = true) : Spells linShape (spellLin S) S := by
  simp only [linB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩,
    b7⟩, b8⟩ := h
  refine Spells.cast (y := S)
    (spells_bind (spells_foldeq a1)
    (spells_bind (spells_word (w_of a2))
    (spells_bind (spells_word (w_of a3))
    (spells_bind (spells_shape a4)
    (spells_bind (spells_shape a5)
    (spells_bind (spells_flag S.omegaRowsHigh)
    (spells_bind (spells_flag S.wRowsHigh)
    (spells_bind (spells_shape a6)
    (spells_bind (spells_shape a7)
    (spells_bind (spells_word (w_of a8))
    (spells_bind (spells_word (w_of a9))
    (spells_bind (spells_word (w_of b1))
    (spells_bind (spells_word (w_of b2))
    (spells_bind (spells_word (w_of b3))
    (spells_bind (spells_word (w_of b4))
    (spells_bind (spells_flag S.masksAhead)
    (spells_bind (spells_stages b5)
    (spells_bind (spells_stages b6)
    (spells_bind (spells_stages b7)
    (spells_bind (spells_stages b8)
    (spells_bind (spells_choice S.choice)
    (spells_pure _)))))))))))))))))))))) ?_
  unfold spellLin
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

/-! ## The binding tree -/

theorem spells_binding {s : LinBindingShape} (h : bindingB s = true) :
    Spells bindingShape (spellBinding s) s := by
  simp only [bindingB, Bool.and_eq_true] at h
  refine Spells.cast
    (spells_bind (spells_word (w_of h.1))
    (spells_bind (spells_word (w_of h.2))
    (spells_pure _))) ?_
  unfold spellBinding
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

/-! ## The ranges -/

theorem spells_run {r : WfRun} (h : runB r = true) : Spells wfRun (spellRun r) r := by
  simp only [runB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine Spells.cast
    (spells_bind (spells_word (w_of h1))
    (spells_bind (spells_word (w_of h2))
    (spells_bind (spells_word (w_of h3))
    (spells_bind (spells_word (w_of h4))
    (spells_pure _))))) ?_
  unfold spellRun
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_empty]

theorem spells_part {p : WfPart} (h : partB p = true) : Spells wfPart (spellPart p) p := by
  simp only [partB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine Spells.cast (y := p) (spells_bind (spells_word (w_of h1)) (spells_bind
    (spells_list (ok := fun x => runB x = true) (fun _ hx => spells_run hx)
      (fun x _ => size_row _ _) (w_of h2) h3) (spells_pure _))) ?_
  unfold spellPart
  simp only [ByteArray.append_empty]

theorem size_part (p : WfPart) : 1 ≤ (spellPart p).size := by
  unfold spellPart spellWord
  rw [ByteArray.size_append, Fmt.size_u64n]
  omega

theorem spells_lookup {l : WfLookup} (h : lookupB l = true) :
    Spells wfLookup (spellLookup l) l := by
  simp only [lookupB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, g1⟩, g2⟩ := h
  refine Spells.cast (y := l) (spells_bind (spells_word (w_of h1)) (spells_bind
    (spells_word (w_of h2)) (spells_bind (spells_word (w_of h3)) (spells_bind
    (spells_list (ok := fun x => eltB x = true) (fun _ hx => spells_elt (e_of hx))
      (fun x _ => by rw [Fmt.elt, Fmt.size_u64]; omega) (w_of h4) h5) (spells_bind
    (spells_elt (e_of h6)) (spells_bind (spells_elt (e_of h7)) (spells_bind
    (spells_list (ok := fun x => partB x = true) (fun _ hx => spells_part hx)
      (fun x _ => size_part x) (w_of h8) h9) (spells_bind
    (spells_list (ok := fun x => wB x = true) (fun _ hx => spells_word (w_of hx))
      (fun x _ => by rw [spellWord, Fmt.size_u64n]; omega) (w_of g1) g2)
    (spells_pure _))))))))) ?_
  unfold spellLookup spellWords
  simp only [spellRow, List.map_cons, List.map_nil, Fmt.cat_cons, Fmt.cat_nil,
    ByteArray.append_assoc, ByteArray.append_empty]

theorem size_lookup (l : WfLookup) : 1 ≤ (spellLookup l).size := by
  unfold spellLookup
  simp only [ByteArray.size_append]
  have := size_row l.d [l.mu, l.live]
  omega

theorem spells_ranges {x : WfPublic} (h : rangesB x = true) :
    Spells wfPublic (spellRanges x) x := by
  simp only [rangesB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine Spells.cast (y := x) (spells_bind
    (spells_list (ok := fun y => lookupB y = true) (fun _ hy => spells_lookup hy)
      (fun y _ => size_lookup y) (w_of h1) h2) (spells_bind (spells_notice h3) (spells_bind
    (spells_word (w_of h4)) (spells_bind (spells_stages h5) (spells_bind
    (spells_choice x.choice) (spells_pure _)))))) ?_
  unfold spellRanges
  simp only [ByteArray.append_assoc, ByteArray.append_empty]

/-! ## The five items' readers -/

theorem readNotice_spell {n : OracleNotice} (h : noticeB n = true) :
    readNotice (spellNotice n) = some n := whole_of_spells (spells_notice h)

theorem readRanges_spell {x : WfPublic} (h : rangesB x = true) :
    readRanges (spellRanges x) = some x := whole_of_spells (spells_ranges h)

theorem readBinding_spell {s : LinBindingShape} (h : bindingB s = true) :
    readBinding (spellBinding s) = some s := whole_of_spells (spells_binding h)

theorem readCodes_spell {c : Codes} (h : codesB c = true) :
    readCodes (spellCodes c) = some c := whole_of_spells (spells_codes h)

theorem readLin_spell {S : LinShape} (h : linB S = true) :
    readLin (spellLin S) = some S := whole_of_spells (spells_lin h)

end Johnson.KB9

#print axioms Johnson.KB9.w_of
#print axioms Johnson.KB9.e_of
#print axioms Johnson.KB9.size_row
#print axioms Johnson.KB9.spells_code
#print axioms Johnson.KB9.spells_codes
#print axioms Johnson.KB9.spells_shape
#print axioms Johnson.KB9.spells_notice
#print axioms Johnson.KB9.spells_stage
#print axioms Johnson.KB9.spells_stages
#print axioms Johnson.KB9.spells_choice
#print axioms Johnson.KB9.spells_index
#print axioms Johnson.KB9.spells_foldeq
#print axioms Johnson.KB9.spells_lin
#print axioms Johnson.KB9.spells_binding
#print axioms Johnson.KB9.spells_run
#print axioms Johnson.KB9.spells_part
#print axioms Johnson.KB9.size_part
#print axioms Johnson.KB9.spells_lookup
#print axioms Johnson.KB9.size_lookup
#print axioms Johnson.KB9.spells_ranges
#print axioms Johnson.KB9.readNotice_spell
#print axioms Johnson.KB9.readRanges_spell
#print axioms Johnson.KB9.readBinding_spell
#print axioms Johnson.KB9.readCodes_spell
#print axioms Johnson.KB9.readLin_spell
