-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayoutOfShapes.lean: THE LAYOUT THAT A STATEMENT GIVES A GROUP WHICH
HOLDS A WRITTEN LIST's MEMBERS AGREES, IN ALL THAT K10's CONDITION READS OF A LAYOUT, WITH THE ONE
AT WHICH THAT CONDITION IS SHOWN: IN PARTICULAR IT HAS NO VARIABLE FOR THE MASK ROWS. A definition,
statements and proofs.

Why. K10's promise asks that the layout which the verifier's state's statement gives the live
frame's group has the typed stage's h (`K10OnU`, KOfYes.lean, beside this file); EndSays.lean and
CubeAt.lean ask more of that layout. LayoutDrawn.lean shows, by the kernel, what `Statement.layout`
gives at a statement MADE OF a written list (`stOf lo kb`), at every choice of kept members; its
`layout_congr` carries that to another statement, but asks its premises at every number, beyond the
members too, where it reads a message that need not be there.
  `laySizes_congr`: two groups with as many members and, AT EACH MEMBER's NUMBER, the same flag,
    "has rows" and bits of rows hand the same sizes to `layBlocks` (`laySizes`, LayBlocks.lean).
  `ShapesAre T G lo kb no`: ONE SENTENCE ON A STATEMENT AND A GROUP: the group's members are the
    list's messages with a main row, in the list's order, under the numbers no; its flags are kb's;
    each member has the written shape.
  `groupOf`, `stOf_group`, `has_of_shape`, `stOf_shape`; `ShapesAre.size`, `.member`, `.flag`,
    `groupOf_member`, `.sizes`: the sizes at T and G are those at `stOf lo kb`.
  `layout_of_shapes`: T.groups[g]? = some G, `ShapesAre`, `LayoutAgrees lo kb`: T.layout g = some L
    with `AgreesWith lo kb L` (Drawn/Def.lean: L.k; L.h = 0; the first main row of each member that
    is not kept; the first mask row of each member that has one), and L's members and flags are G's.
  `layout_full`, `layout_small`: at the 26 and the 6 written lists, whichever members are kept: L.h
    = 0 and L.k = `kLay lo kb`, in front of the beginning of the group's test and behind it
    (`begun_layout`, LayBegun.lean).
Limits. `ShapesAre` IS SHOWN OF NO STATE: that the open group's members with their flags are the
frame's lists, and that a message has the shape which its sending announced, are two invariants
along the chain which, as far as is known here, are not typed. On the two codes'
lengths (the layout's two exponents) nothing is said here. `CubeFits` (CubeAt.lean) is not drawn
here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayoutDrawn
import Johnson.Desc.First.Close.Law.LayBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open OnBytes.LayLaw (laySizes layout_eq begun_layout)

/-- Two groups with as many members and, AT EACH MEMBER's NUMBER, the same flag, "has rows" and bits
of rows hand the same sizes to layBlocks. -/
theorem laySizes_congr (T T' : Statement) (G G' : Group) (hn : G.members.size = G'.members.size)
    (hk : ∀ i, i < G.members.size → G.kept.getD i false = G'.kept.getD i false)
    (hh : ∀ i, i < G.members.size → ∀ part,
      T.has (G.members.getD i noId) part = T'.has (G'.members.getD i noId) part)
    (hb : ∀ i, i < G.members.size → ∀ part,
      T.rowBits (G.members.getD i noId) part = T'.rowBits (G'.members.getD i noId) part)
    (part : Part) : laySizes T G part = laySizes T' G' part := by
  unfold laySizes
  rw [← hn]
  apply Array.map_congr_left
  intro i hi
  have hi' : i < G.members.size := by simpa using hi
  simp only [hk i hi', hh i hi', hb i hi']

/-- **A statement's group holds a written list's members**: the group's members are the list's
messages with a main row, in the list's order, under the numbers no; its flags are kb's; each member
has the written shape. -/
structure ShapesAre (T : Statement) (G : Group) (lo : List (OracleShape × ℕ))
    (kb : Fin lo.length → Bool) (no : Fin lo.length → ℕ) : Prop where
  members : G.members.toList = (membersOf lo).map no
  kept : G.kept.toList = (membersOf lo).map kb
  shape : ∀ i ∈ membersOf lo, (T.oracles[no i]?).map (fun x : Oracle => x.shape) = some (lo.get i).1

/-- The one group of the statement made of a list. -/
abbrev groupOf (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) : Group :=
  { code := 0, members := ((membersOf lo).map fun i => i.val).toArray
    kept := ((membersOf lo).map kb).toArray }

theorem stOf_group (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) :
    (stOf lo kb).groups[0]? = some (groupOf lo kb) := rfl

theorem has_of_shape {T : Statement} {o : ℕ} {sh : OracleShape}
    (h : (T.oracles[o]?).map (fun x : Oracle => x.shape) = some sh) (part : Part) :
    T.has o part = decide (0 < sh.rows part) ∧ T.rowBits o part = ceilLog2 (sh.rows part) := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Statement.has Statement.rowBits
  rw [hx]
  exact ⟨rfl, rfl⟩

theorem stOf_shape (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (i : Fin lo.length) :
    ((stOf lo kb).oracles[i.val]?).map (fun x : Oracle => x.shape) = some (lo.get i).1 := by
  unfold stOf
  simp

section
variable {T : Statement} {G : Group} {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool}
  {no : Fin lo.length → ℕ}

theorem ShapesAre.size (H : ShapesAre T G lo kb no) : G.members.size = (membersOf lo).length := by
  rw [← Array.length_toList, H.members, List.length_map]

theorem ShapesAre.member (H : ShapesAre T G lo kb no) {i : ℕ} (hi : i < (membersOf lo).length) :
    G.members.getD i noId = no (membersOf lo)[i] := by
  have e : G.members[i]? = some (no (membersOf lo)[i]) := by
    rw [← Array.getElem?_toList, H.members, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  rw [Array.getD_eq_getD_getElem?, e]
  rfl

theorem ShapesAre.flag (H : ShapesAre T G lo kb no) (i : ℕ) :
    G.kept.getD i false = (groupOf lo kb).kept.getD i false := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, H.kept]
  simp

theorem groupOf_member (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) {i : ℕ}
    (hi : i < (membersOf lo).length) :
    (groupOf lo kb).members.getD i noId = ((membersOf lo)[i]).val := by
  rw [Array.getD_eq_getD_getElem?]
  simp [hi]

/-- The sizes that the layout hands to layBlocks are those at the statement made of the list. -/
theorem ShapesAre.sizes (H : ShapesAre T G lo kb no) (part : Part) :
    laySizes T G part = laySizes (stOf lo kb) (groupOf lo kb) part := by
  have hn : G.members.size = (groupOf lo kb).members.size := by
    rw [H.size]
    simp
  refine laySizes_congr T (stOf lo kb) G (groupOf lo kb) hn (fun i _ => H.flag i) ?_ ?_ part
  · intro i hi p
    have hi' : i < (membersOf lo).length := H.size ▸ hi
    rw [H.member hi', groupOf_member lo kb hi',
      (has_of_shape (H.shape _ (List.getElem_mem hi')) p).1,
      (has_of_shape (stOf_shape lo kb _) p).1]
  · intro i hi p
    have hi' : i < (membersOf lo).length := H.size ▸ hi
    rw [H.member hi', groupOf_member lo kb hi',
      (has_of_shape (H.shape _ (List.getElem_mem hi')) p).2,
      (has_of_shape (stOf_shape lo kb _) p).2]

/-- **THE LAYOUT OF A GROUP THAT HOLDS A WRITTEN LIST's MEMBERS AGREES WITH THE ONE AT WHICH K10's
CONDITION IS SHOWN.** -/
theorem layout_of_shapes {g : ℕ} (hG : T.groups[g]? = some G) (H : ShapesAre T G lo kb no)
    (hA : LayoutAgrees lo kb) :
    ∃ L, T.layout g = some L ∧ AgreesWith lo kb L ∧ L.members = G.members ∧ L.kept = G.kept := by
  unfold LayoutAgrees at hA
  rw [layout_eq (stOf lo kb) 0 (groupOf lo kb) (stOf_group lo kb)] at hA
  refine ⟨_, layout_eq T g G hG, ?_, rfl, rfl⟩
  unfold AgreesWith at hA ⊢
  simp only [H.sizes]
  exact hA

/-- **AT THE WRITTEN LISTS OF THE FULL SIZE, WHICHEVER MEMBERS ARE KEPT**: the layout has no
variable for the mask rows, and the formula's number of row variables; in front of the beginning of
the group's test and behind it. -/
theorem layout_full {g : ℕ} (hlo : lo ∈ linksFullLit) (hG : T.groups[g]? = some G)
    (H : ShapesAre T G lo kb no) :
    ∃ L, T.layout g = some L ∧ (begun T g G).layout g = some L ∧ L.h = 0 ∧ L.k = kLay lo kb ∧
      L.members = G.members ∧ L.kept = G.kept := by
  obtain ⟨L, h1, h2, h3, h4⟩ := layout_of_shapes hG H (linksFull_layout lo hlo kb)
  exact ⟨L, h1, (begun_layout T g G hG).trans h1, h2.2.1, h2.1, h3, h4⟩

/-- The like at the small size. -/
theorem layout_small {g : ℕ} (hlo : lo ∈ linksSmallLit) (hG : T.groups[g]? = some G)
    (H : ShapesAre T G lo kb no) :
    ∃ L, T.layout g = some L ∧ (begun T g G).layout g = some L ∧ L.h = 0 ∧ L.k = kLay lo kb ∧
      L.members = G.members ∧ L.kept = G.kept := by
  obtain ⟨L, h1, h2, h3, h4⟩ := layout_of_shapes hG H (linksSmall_layout lo hlo kb)
  exact ⟨L, h1, (begun_layout T g G hG).trans h1, h2.2.1, h2.1, h3, h4⟩

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.layout_of_shapes
#print axioms VerifiableInference.Desc.First.Close.layout_full
#print axioms VerifiableInference.Desc.First.Close.layout_small
#print axioms VerifiableInference.Desc.First.Close.laySizes_congr
