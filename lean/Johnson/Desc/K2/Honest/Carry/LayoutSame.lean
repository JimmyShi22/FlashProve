-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/LayoutSame.lean: THE LAYOUT THAT `foldEnd`
(Johnson/Desc/K2/Honest/FoldEnd.lean) MAKES ANEW OF A GROUP's MEMBERS' TRUE SHAPES HAS THE FOUR
FIELDS THAT A FOLD READS OF THE DESCRIPTION's OWN LAYOUT OF THE GROUP (`layoutOf`,
Johnson/Desc/Own/Layout.lean). SO THE CLAIM AT WHAT `foldEnd` LEAVES OF ROWS IN FULL IS THE CLAIM AT
`leftAt` OF THE WORDS (Johnson/Desc/K2/Honest/Carry/Left.lean), WHERE THE CARRIED ROWS' LAYOUT HAS
THESE FOUR FIELDS. For whoever spends the exact carry at what an honest prover's closing returns.
None of its Lean terms is a state, a way in, a front or a witness (the letter w stands for words
that a caller hands). Two short names; statements with their proofs.

  `bareSt` with `bareGroup`: short names for `groupLayout`'s own inner terms: the statement that
                    holds the members' shapes alone; the group whose members are their places
  `blockBits_true` the blocks' sizes (`blockBits`) are the same at these two and at the statement
                    and the group themselves: where the carried rows' layout has the group's members
                    and flags, and the group's two lists are of one length
  `groupLayout_true` so `groupLayout … (membersTrue S old)` has `layoutOf S G`'s k · h · mainFirst ·
                    maskFirst
  `claimTrue_of_foldEnd` THE JOIN: these three premises · the carried rows' layout has `layoutOf S
                    G`'s four fields · the three premises of `claimTrue_of_rows` (Carry/OfRows.lean)
                    on the rows' entries ⊢ `ClaimTrue` at `leftAt S old w` ↔ `ClaimTrue` at `foldEnd
                    S.codes old.code old.maskCode (membersTrue S old) M fresh ‹the carried rows'
                    challenges›`

By: `foldEnd_eq_at` (Carry/Left.lean) · `foldEndAt_lay`, `claimTrue_of_rows`, `membersTrue`
(Carry/OfRows.lean) · the definitions. NEAR, NOT CALLED: the library's `layout_congr`
(Johnson/Desc/First/Close/Law/LayoutDrawn.lean): "a layout hangs on little": two statements whose
groups have as many members, the same flags and, member by member, the same "has rows" and the same
bits of rows have layouts with these very four fields alike: BUT OF THE PROGRAM's `Statement.layout`
AT GROUPS THAT STAND IN BOTH STATEMENTS: the statement that `groupLayout` makes holds no group: so
it cannot be called as it stands · `layoutOf_extends` (Johnson/Desc/Means/Keeps.lean): the layout
stays where a statement is extended: another road. A HOMONYM: `blockBits` in OnBytes/Iop/Lin.lean is
another notion.

Limits. ALL PREMISES ARE PREMISES: SEVEN PUBLIC ONES ON THE LAYOUT AND THE GROUP, three on the rows'
entries: shown of no state and no run. That a closing's record has the description's layout of the
closed group is not proved here (Johnson/Desc/K2/Honest/Returns/LayoutReached.lean has the seven at
reached states). THE JOIN HAS ONE LETTER S, for the layout and for `leftAt`, `sizesAt`,
`membersTrue` alike: it is meant to be spent at the closing's statement; the exact carry speaks at a
later front's: `leftAt_same` and `sizesAt_same` (Carry/Exact.lean) carry two of the three there;
nothing here carries `membersTrue` there. THE MEMBERS ARE `membersTrue`: read off the statement and
the carried rows; an honest prover's closing takes its members, rows and challenges off a plan,
coins and what it heard: NOTHING HERE TIES THESE. The layout's other fields (the two logarithms of
lengths, the members, the flags) are not compared: a fold does not read them. Nothing on tails, pads
or symbols. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Carry.OfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE formAt)
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows)

/-- The statement that `groupLayout` makes: the members' shapes alone. -/
abbrev bareSt (codes : Codes) (ms : List GroupMember) : Statement :=
  { codes := codes, oracles := (ms.map fun m => { shape := m.shape }).toArray }

/-- The group that `groupLayout` makes: the members by their places. -/
abbrev bareGroup (code maskCode : Nat) (ms : List GroupMember) : Group :=
  { code := code, maskCode := maskCode, members := Array.range ms.length
    kept := (ms.map (·.kept)).toArray }

/-- **The blocks' sizes are the same**: at the statement of the members' true shapes, the members by
their places; and at the statement itself, the members by their numbers. -/
theorem blockBits_true (S : Statement) (G : Group) (old : SingleRows)
    (hm : old.layout.members = G.members) (hk : old.layout.kept = G.kept)
    (hs : G.kept.size = G.members.size) (part : Part) :
    Own.blockBits (bareSt S.codes (membersTrue S old))
      (bareGroup old.code old.maskCode (membersTrue S old)) part = Own.blockBits S G part := by
  have hn : (membersTrue S old).length = G.members.size := by
    unfold membersTrue
    rw [List.length_map, Array.length_toList, Array.size_zip, hm, hk, hs, Nat.min_self]
  unfold Own.blockBits
  apply Array.ext
  · simp [hn]
  · intro i h1 h2
    have hi : i < G.members.size := by simpa using h2
    have hi2 : i < G.kept.size := hs ▸ hi
    have hl : (old.layout.members.zip old.layout.kept).toList[i]? =
        some (G.members[i], G.kept[i]) := by
      rw [hm, hk, Array.toList_zip, List.getElem?_zip_eq_some]
      exact ⟨by simp [hi], by simp [hi2]⟩
    have hT : (membersTrue S old)[i]? =
        some ⟨(S.oracles.getD G.members[i] default).shape, G.kept[i]⟩ := by
      unfold membersTrue
      rw [List.getElem?_map, hl]
      rfl
    have f1 : (bareGroup old.code old.maskCode (membersTrue S old)).members.getD i noId = i := by
      show (Array.range (membersTrue S old).length).getD i noId = i
      rw [hn, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi),
        Array.getElem_range]
      rfl
    have f2 : (bareGroup old.code old.maskCode (membersTrue S old)).kept.getD i false =
        G.kept.getD i false := by
      show ((membersTrue S old).map (·.kept)).toArray.getD i false = _
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getElem?_map, hT, Array.getElem?_eq_getElem hi2]
      rfl
    have f3 : (bareSt S.codes (membersTrue S old)).oracles[i]? =
        some { shape := (S.oracles.getD G.members[i] default).shape } := by
      show ((membersTrue S old).map fun m =>
        ({ shape := m.shape } : OnBytes.Oracle)).toArray[i]? = _
      rw [List.getElem?_toArray, List.getElem?_map, hT]
      rfl
    have f4 : G.members.getD i noId = G.members[i] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      rfl
    rw [Array.getElem_map, Array.getElem_map, Array.getElem_range, Array.getElem_range]
    dsimp only
    rw [f1, f2, f4]
    unfold Own.tableThere Statement.rowBits
    rw [f3, Array.getD_eq_getD_getElem?]
    cases S.oracles[G.members[i]]? with
    | none => cases part <;> rfl
    | some x => rfl

/-- **THE LAYOUT THAT `foldEnd` MAKES ANEW OF THE MEMBERS' TRUE SHAPES HAS THE FOUR READ FIELDS OF
THE DESCRIPTION's OWN LAYOUT OF THE GROUP.** -/
theorem groupLayout_true (S : Statement) (G : Group) (old : SingleRows)
    (hm : old.layout.members = G.members) (hk : old.layout.kept = G.kept)
    (hs : G.kept.size = G.members.size) :
    (groupLayout S.codes old.code old.maskCode (membersTrue S old)).k = (Own.layoutOf S G).k ∧
      (groupLayout S.codes old.code old.maskCode (membersTrue S old)).h = (Own.layoutOf S G).h ∧
      (groupLayout S.codes old.code old.maskCode (membersTrue S old)).mainFirst =
        (Own.layoutOf S G).mainFirst ∧
      (groupLayout S.codes old.code old.maskCode (membersTrue S old)).maskFirst =
        (Own.layoutOf S G).maskFirst := by
  have b1 := blockBits_true S G old hm hk hs .main
  have b2 := blockBits_true S G old hm hk hs .mask
  unfold groupLayout Own.layoutOf
  dsimp only
  rw [b1, b2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **THE CLAIM AT WHAT `foldEnd` LEAVES OF ROWS IN FULL IS THE CLAIM AT `leftAt` OF THE WORDS**,
where the carried rows' layout has the four read fields of the description's own layout of the
group. -/
theorem claimTrue_of_foldEnd (S : Statement) (G : Group) (old : SingleRows) (T : SwitchTarget)
    (w : Words GE) (M : Nat → Rows) (fresh : Rows)
    (hm : old.layout.members = G.members) (hk : old.layout.kept = G.kept)
    (hs : G.kept.size = G.members.size)
    (l1 : old.layout.k = (Own.layoutOf S G).k) (l2 : old.layout.h = (Own.layoutOf S G).h)
    (l3 : old.layout.mainFirst = (Own.layoutOf S G).mainFirst)
    (l4 : old.layout.maskFirst = (Own.layoutOf S G).maskFirst)
    (hM : ∀ i b j, i < old.layout.members.size →
      b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows →
      (M i).main
          ((S.oracles.getD (old.layout.members.getD i noId) default).shape.mainDeg == 3) b j =
        w (old.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
          (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows))
    (hZ : ∀ i b j, i < old.layout.members.size →
      b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows →
      (M i).mask b j = w (old.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
        (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows))
    (hF : ∀ b j, b < 2 ^ old.layout.h → fresh.mask b j = w old.fresh .mask
      (b + j * 2 ^ ceilLog2 (S.oracles.getD old.fresh default).shape.maskRows)) :
    ClaimTrue (sizesAt S old T) old (leftAt S old w) ↔
      ClaimTrue (sizesAt S old T) old (foldEnd S.codes old.code old.maskCode
        (membersTrue S old) M fresh (old.gamma.map readE)) := by
  obtain ⟨g1, g2, g3, g4⟩ := groupLayout_true S G old hm hk hs
  rw [foldEnd_eq_at, foldEndAt_lay old.layout _ (g1.trans l1.symm) (g2.trans l2.symm)
    (g3.trans l3.symm) (g4.trans l4.symm)]
  exact claimTrue_of_rows S old T w M fresh (by rw [hm, hk]; exact hs) hM hZ hF

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.blockBits_true
#print axioms VerifiableInference.Desc.K2.Honest.groupLayout_true
#print axioms VerifiableInference.Desc.K2.Honest.claimTrue_of_foldEnd
#print axioms VerifiableInference.Desc.K2.Honest.bareSt
#print axioms VerifiableInference.Desc.K2.Honest.bareGroup
