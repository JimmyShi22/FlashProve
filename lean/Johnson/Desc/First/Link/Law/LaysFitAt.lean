-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LaysFitAt.lean: `LaysFit R L ix` (MainTable.lean: "the layout fits the
typed
group, member by member") AT THE TYPED GROUP AT THE PROGRAM's OWN LAYOUT OF A WRITTEN LIST, R :=
`groupLayK cs lo s e kb hM hZ` (Johnson/Desc/First/Close/Law/CubeOfShapes.lean), AND ix a := `posOf
lo
a.1` (where the message stands among the list's members). Statements and proofs: short, over that
file's lemmas.

  `pos_onto`: every number below the number of members is a member's place.
  `pos_inj`: two members with one place are one.
  `laysFit_at`: **ShapesAre T G lo kb no · L.members = G.members · L.kept = G.kept · AgreesWith lo
kb L
    ⊢ LaysFit (groupLayK cs lo s e kb hM hZ) L fun a => posOf lo a.1**: ALL SIX FIELDS. lt:
`pos_lt`;
    inj: `pos_inj`; onto: `pos_onto`; unkept, free: `flag_pos` and `Rows.keep_slot_none`; first: the
    third clause of `AgreesWith` (Johnson/Desc/First/Close/Law/Drawn/Def.lean): an unkept member's
    first main row in the layout IS the corner that the typed group has.
  `laysFit_of_shapes`: **so, from T.groups[g]? = some G, ShapesAre and `LayoutAgrees lo kb` alone:
there
    is the statement's own layout L of group g, and it fits** (by `layout_of_shapes`,
    LayoutOfShapes.lean).
Limits. `ShapesAre` at a reached state (the state's group holds the written list's members) is
a
debt; `LayoutAgrees lo kb` at the written lists is `linksFull_layout`. That the
numbering parts the members is NOT asked here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.MainTable
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.First.Close

/-- Every number below the number of members is a member's place. -/
theorem pos_onto (lo : List (OracleShape × ℕ)) {w : ℕ} (hw : w < (membersOf lo).length) :
    posOf lo ((membersOf lo)[w]) = w := by
  have hm : (membersOf lo)[w] ∈ membersOf lo := List.getElem_mem hw
  have e := (List.getElem?_eq_some_iff.1 (pos_get lo _ hm)).2
  exact (List.Nodup.getElem_inj_iff (members_nodup lo)).1 e

/-- Two members with one place are one. -/
theorem pos_inj (lo : List (OracleShape × ℕ)) {i j : Fin lo.length} (hi : i ∈ membersOf lo)
    (hj : j ∈ membersOf lo) (e : posOf lo i = posOf lo j) : i = j := by
  have h1 := pos_get lo i hi
  rw [e, pos_get lo j hj] at h1
  exact (Option.some.inj h1).symm

section
variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {e : ℕ} {kb : Fin lo.length → Bool}
  {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C}
  {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z}
  {T : Statement} {G : Group} {no : Fin lo.length → ℕ} {L : GroupLayout}

/-- **THE LAYOUT FITS THE TYPED GROUP, MEMBER BY MEMBER.** -/
theorem laysFit_at (H : ShapesAre T G lo kb no) (hLm : L.members = G.members)
    (hLk : L.kept = G.kept) (hA : AgreesWith lo kb L) :
    LaysFit (groupLayK cs lo s e kb hM hZ) L fun a => posOf lo a.1 := by
  have hmem : ∀ a : {i // memMain lo i}, a.1 ∈ membersOf lo := fun a => mem_members.2 a.2
  have hsz : L.members.size = (membersOf lo).length := by rw [hLm, H.size]
  have hflag : ∀ a : {i // memMain lo i}, L.kept.getD (posOf lo a.1) false = kb a.1 := fun a => by
    rw [hLk, flag_pos H (hmem a)]
  refine ⟨fun a => ?_, fun a b hab => ?_, fun w hw => ?_, fun r hr => ?_, fun a ha j => ?_,
    fun a ha => ?_⟩
  · rw [hsz]
    exact pos_lt lo a.1 (hmem a)
  · exact Subtype.ext (pos_inj lo (hmem a) (hmem b) hab)
  · rw [hsz] at hw
    exact ⟨⟨(membersOf lo)[w], mem_members.1 (List.getElem_mem hw)⟩, pos_onto lo hw⟩
  · rw [hflag r.1]
    have := (Rows.keep_slot_none _ _ _).1 hr
    simpa using this
  · rw [hflag a] at ha
    exact (Rows.keep_slot_none _ _ _).2 (by simp [ha])
  · rw [hflag a] at ha
    exact hA.2.2.1 a.1 a.2 ha

/-- **FROM THE STATEMENT's OWN LAYOUT.** -/
theorem laysFit_of_shapes {g : ℕ} (hG : T.groups[g]? = some G) (H : ShapesAre T G lo kb no)
    (hLA : LayoutAgrees lo kb) :
    ∃ L, T.layout g = some L ∧
      LaysFit (groupLayK cs lo s e kb hM hZ) L fun a => posOf lo a.1 := by
  obtain ⟨L, h1, h2, h3, h4⟩ := layout_of_shapes hG H hLA
  exact ⟨L, h1, laysFit_at H h3 h4 h2⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pos_onto
#print axioms VerifiableInference.Desc.LinkJoin.pos_inj
#print axioms VerifiableInference.Desc.LinkJoin.laysFit_at
#print axioms VerifiableInference.Desc.LinkJoin.laysFit_of_shapes
