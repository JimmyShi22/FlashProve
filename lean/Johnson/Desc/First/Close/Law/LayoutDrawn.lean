-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayoutDrawn.lean: THE LAYOUT AT WHICH K10's CONDITION IS SHOWN IS THE
PROGRAM's `Statement.layout` ITSELF. Definitions, statements and proofs. NO TEXT OF THE DESCRIPTION
STANDS BENEATH THIS FILE.

Corners.lean (beside this file) types the program's layout AFTER `Statement.layout`
(OnBytes/Iop/Ground.lean:1118): `layAt`, `sizesM`, `sizesZ`, `kLay`.
Corners.lean has no lemma that ties them to it. Here is the tie, in two halves.
  `membersOf`, `stOf lo kb`, `posOf`: a statement made of a list's shapes, with one group: its
    members the messages with a main row, in the list's order, with the flags kb.
  `AgreesWith lo kb L`, `LayoutAgrees lo kb`: `Statement.layout` at that statement gives a layout L
    with: L.k = `kLay lo kb`; L.h = 0; at each member that is not kept, L.mainFirst is `layAt
    (sizesM lo kb)`; at each member with a mask row, L.maskFirst is `layAt (sizesZ lo)`. Decidable.
  `linksFull_layout`, `linksSmall_layout`: SO IT IS at each of the 26 and the 6 written lists, at
    EVERY choice of kept members. By evaluation of the program's own function in the kernel, a list
    at a time (`LayoutAll`; the lists without repeats are five at each size).
  `layout_congr`: a layout hangs on little: two statements whose groups have as many members, the
    same flags and, member by member, the same "has rows" and the same bits of rows have one k, h,
    mainFirst and maskFirst. So what is shown at `stOf lo kb` holds of every statement whose group
    has these members' shapes and flags.
Who joins a link's group, and who is kept there: by the program's text, read in a
state of this library other than this one, not
proved; TWO RULES.
(1) `joinOwn` (OnBytes/Iop/Req.lean:300): each of the link's own messages joins, kept if
its life is above 0. (2) From the second link on the link's first message goes through the code
switch, whose `switchAdmit` (OnBytes/Iop/Cs.lean:539) joins g, the carrying message, not kept, and
each message that takes an earlier message's kept rows, with the flag keptAgain; `reqGroupAt`
(Req.lean:83) sets that flag where more than one link is left to the earlier message. The one
written message without a main row (in the first list at each size: one mask row, sampled) has the
shape that `reqShapeOk` asks of a message "at start", which OnBytes/Iop/Lin.lean calls "in no link's
group". The statements here run over EVERY choice of flags: none leans on who is kept. WHO THE
MEMBERS ARE they take from the written lists: the messages with a main row.
Limits. That a running statement's group has just these members, shapes and flags at a closing is
not shown: `layout_congr`'s premises are owed by whoever has the plan's tie. The messages that a
code switch lays into a group are taken as the written lists have them. `Statement.layout` is the
program's; that the description's own layout (Johnson/Desc/Own/Layout.lean) agrees with it is
other files' to show. Nothing on soundness of the protocol.

-/
import Johnson.Desc.First.Close.Law.Drawn.Full0a
import Johnson.Desc.First.Close.Law.Drawn.Full0b
import Johnson.Desc.First.Close.Law.Drawn.Full1a
import Johnson.Desc.First.Close.Law.Drawn.Full1b
import Johnson.Desc.First.Close.Law.Drawn.Full1c
import Johnson.Desc.First.Close.Law.Drawn.Full1d
import Johnson.Desc.First.Close.Law.Drawn.Full2a
import Johnson.Desc.First.Close.Law.Drawn.Full2b
import Johnson.Desc.First.Close.Law.Drawn.Full34
import Johnson.Desc.First.Close.Law.Drawn.Small0a
import Johnson.Desc.First.Close.Law.Drawn.Small0b
import Johnson.Desc.First.Close.Law.Drawn.Small1a
import Johnson.Desc.First.Close.Law.Drawn.Small1b
import Johnson.Desc.First.Close.Law.Drawn.Small1c
import Johnson.Desc.First.Close.Law.Drawn.Small1d
import Johnson.Desc.First.Close.Law.Drawn.Small2a
import Johnson.Desc.First.Close.Law.Drawn.Small2b
import Johnson.Desc.First.Close.Law.Drawn.Small34

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

/-! The written lists without repeats are five at each size: the evaluations stand in the files of
the folder Drawn/, so that none is heavy. -/

theorem layoutFull_0 : LayoutAll (linksFullLit.dedup.getD 0 []) :=
  layoutAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact layoutFull_0_0
    · exact layoutFull_0_1
    · exact layoutFull_0_2
    · exact layoutFull_0_3

theorem layoutFull_1 : LayoutAll (linksFullLit.dedup.getD 1 []) :=
  layoutAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact layoutFull_1_0
    · exact layoutFull_1_1
    · exact layoutFull_1_2
    · exact layoutFull_1_3

theorem layoutFull_2 : LayoutAll (linksFullLit.dedup.getD 2 []) :=
  layoutAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact layoutFull_2_0
    · exact layoutFull_2_1
    · exact layoutFull_2_2
    · exact layoutFull_2_3

theorem layoutFull_len : linksFullLit.dedup.length = 5 := by
  decide +kernel

theorem layoutFull_each (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) :
    LayoutAll lo := by
  refine each_of_getD LayoutAll _ [] 5 layoutFull_len (fun i hi => ?_) lo (List.mem_dedup.2 hlo)
  interval_cases i
  · exact layoutFull_0
  · exact layoutFull_1
  · exact layoutFull_2
  · exact layoutFull_3
  · exact layoutFull_4

theorem layoutSmall_0 : LayoutAll (linksSmallLit.dedup.getD 0 []) :=
  layoutAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact layoutSmall_0_0
    · exact layoutSmall_0_1
    · exact layoutSmall_0_2
    · exact layoutSmall_0_3

theorem layoutSmall_1 : LayoutAll (linksSmallLit.dedup.getD 1 []) :=
  layoutAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact layoutSmall_1_0
    · exact layoutSmall_1_1
    · exact layoutSmall_1_2
    · exact layoutSmall_1_3

theorem layoutSmall_2 : LayoutAll (linksSmallLit.dedup.getD 2 []) :=
  layoutAll_of_if fun b0 b1 => by
    cases b0 <;> cases b1
    · exact layoutSmall_2_0
    · exact layoutSmall_2_1
    · exact layoutSmall_2_2
    · exact layoutSmall_2_3

theorem layoutSmall_len : linksSmallLit.dedup.length = 5 := by
  decide +kernel

theorem layoutSmall_each (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) :
    LayoutAll lo := by
  refine each_of_getD LayoutAll _ [] 5 layoutSmall_len (fun i hi => ?_) lo (List.mem_dedup.2 hlo)
  interval_cases i
  · exact layoutSmall_0
  · exact layoutSmall_1
  · exact layoutSmall_2
  · exact layoutSmall_3
  · exact layoutSmall_4

/-- **AT EVERY WRITTEN LIST AND EVERY CHOICE OF KEPT MEMBERS THE PROGRAM's `Statement.layout` SAYS
WHAT Corners.lean's DEFINITIONS SAY.** -/
theorem linksFull_layout : ∀ lo ∈ linksFullLit, ∀ kb : Fin lo.length → Bool,
    LayoutAgrees lo kb :=
  layoutFull_each

theorem linksSmall_layout : ∀ lo ∈ linksSmallLit, ∀ kb : Fin lo.length → Bool,
    LayoutAgrees lo kb :=
  layoutSmall_each

/-- **A layout hangs on little**: two statements whose groups have as many members, the same flags
and, member by member, the same "has rows" and the same bits of rows, have one layout but for the
members' numbers and the codes' lengths. -/
theorem layout_congr (S S' : Statement) (g g' : ℕ) (G G' : Group) (hG : S.groups[g]? = some G)
    (hG' : S'.groups[g']? = some G') (hn : G.members.size = G'.members.size)
    (hk : ∀ i, G.kept.getD i false = G'.kept.getD i false)
    (hh : ∀ i part, S.has (G.members.getD i noId) part = S'.has (G'.members.getD i noId) part)
    (hb : ∀ i part,
      S.rowBits (G.members.getD i noId) part = S'.rowBits (G'.members.getD i noId) part) :
    ∃ L L', S.layout g = some L ∧ S'.layout g' = some L' ∧ L.k = L'.k ∧ L.h = L'.h ∧
      L.mainFirst = L'.mainFirst ∧ L.maskFirst = L'.maskFirst := by
  unfold Statement.layout
  rw [hG, hG']
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [hn, hk, hh, hb, and_self]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.linksFull_layout
#print axioms VerifiableInference.Desc.First.Close.linksSmall_layout
#print axioms VerifiableInference.Desc.First.Close.layout_congr
