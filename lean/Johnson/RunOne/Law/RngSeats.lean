-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngSeats.lean: THE SEATS OF THE GROUP THAT THE KIND K12's LAW NAMES ARE THE LAYOUT's: so the word of which that law speaks has rows of zeros wherever no member has a real row. Statements and proofs.
OBJECT. `gpG`, the typed group that the kind's law makes of the record's plain data, against the layout that the statement gives the group.
USER. Johnson/RunOne/Law/RngCond.lean (rowsBlank_gp).
LETTERS. General in the place. What is asked by name stands below.

The setting. The kind's own files have two chains of lemmas on the word y of the group under test. The kind's law reads y off the members' written trees, as the word of a typed group that it makes of the record's plain data (`gpG`). What the batched claim
means is said of any word with `RowsBlank` (0 in every row that is no member's real row), which Johnson/Desc/K12/Law/RowsBlankWord.lean shows of a typed group's word under `SeatsAre` ("the seats are the layout's") and says: "`SeatsAre` is shown here of no group"; until it stands of
the group that the law names, the two chains speak of two words y that are not shown to be one.

What is said.
  `find_at`: in a layout without a member twice, the member that stands at place i is found at place i.
  `seatsAre_of`: FOR ANY TYPED GROUP, at plain functions: the layout's clauses, the numbers of rows, no member twice, and each member's shape in the statement: `SeatsAre`. `seatsAre_of_lay`: the same at the library's public data of a group (`GpData`, `LayG`).
  `seatsAre_gp`: of `gpG`, from what the test gpOk gives (`Good`, `Made`).
  `shapes_made`: at the plain data's own statement each member has its shape.
  `numbered_gp`: that group's seats are by numbers, with room, and apart (`Gp.Numbered`), from `Good` alone: as in gp_pub (Johnson/Desc/K12/Law/FirstOkLaw.lean).
  `rowsBlank_gp`: SO `RowsBlank` OF THAT GROUP's WORD, at all members' words.
What is asked, by name. hnd: no member twice in the layout (the test combineAt gives it of the group, whose members the layout has). hsh: at the statement S each member has the shape that the plain data hold (where the first fold's mask has come earlier,
the plain data's statement IS the statement behind the batching). Fa: the layout's facts (from combineAt's yes). hk, hh: two of the layout's four numbers.
Limits. General in the place: nothing here is a key file's alone. Nothing on the members' own words, on how they are read off trees, or on a view. Nothing on soundness.

-/
import Johnson.Desc.K12.Law.RowsBlankWord
import Johnson.Desc.K12.Law.FirstOkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngSeats
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means
open H2K.ClaimSays (SeatsAre RowsBlank rowsBlank_word)
open H2K.First (Good Made Plain gpG gpP gp_lay gp_pub oM oZ sg)
open VerifiableInference.Desc.K12 (P12 T12)

/-- In a layout without a member twice, the member that stands at place i is found at place i. -/
theorem find_at {L : GroupLayout} (hnd : L.members.toList.Nodup) {i o : Nat}
    (h : L.members[i]? = some o) : L.find o = some i := by
  have hl : L.members.toList[i]? = some o := by rw [Array.getElem?_toList]; exact h
  obtain ⟨j, hj⟩ := find_of_mem (L := L) (List.mem_of_getElem? hl)
  obtain ⟨hjlt, hjo⟩ := find_some hj
  have e1 : L.members.toList[j]? = some o := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem hjlt]
    simpa [Array.getD, hjlt] using hjo
  have e2 : j = i := List.getElem?_inj (by simpa using hjlt) hnd (e1.trans hl.symm)
  rw [← e2]
  exact hj

/-- **For any typed group**, at plain functions: each member's number, its place in the layout, its shape, the first rows of its two blocks. -/
theorem seatsAre_of {s : Sg} {G : Gp s} (id ix oM oZ : G.ι → ℕ) (sh : G.ι → OracleShape) {L : GroupLayout}
    (hmem : ∀ i, L.members[ix i]? = some (id i)) (hkept : ∀ w, L.kept.getD w false = false)
    (hMF : ∀ i, 0 < (G.mb i).nM → L.mainFirst.getD (ix i) none = some (oM i))
    (hZF : ∀ i, 0 < (G.mb i).nZ → L.maskFirst.getD (ix i) none = some (oZ i))
    (hnd : L.members.toList.Nodup) (S : Statement)
    (hsh : ∀ i, ∃ x, S.oracles[id i]? = some x ∧ x.shape = sh i)
    (hM : ∀ i, (sh i).mainRows = (G.mb i).nM) (hZ : ∀ i, (sh i).maskRows = (G.mb i).nZ) :
    SeatsAre G oM oZ S L where
  at_ := fun i => by
    obtain ⟨x, hx, ex⟩ := hsh i
    refine ⟨id i, ix i, find_at hnd (hmem i), hkept _, ?_, ?_, hMF i, hZF i⟩
    · unfold realRows
      rw [hx]
      show x.shape.mainRows = _
      rw [ex]
      exact hM i
    · unfold realRows
      rw [hx]
      show x.shape.maskRows = _
      rw [ex]
      exact hZ i

/-- The same at the library's public data of a typed group. -/
theorem seatsAre_of_lay {s : Sg} {G : Gp s} (P : GpData G) {L : GroupLayout} (hL : P.LayG L)
    (hnd : L.members.toList.Nodup) (S : Statement)
    (hsh : ∀ i, ∃ x, S.oracles[P.id i]? = some x ∧ x.shape = P.sh i)
    (hM : ∀ i, (P.sh i).mainRows = (G.mb i).nM) (hZ : ∀ i, (P.sh i).maskRows = (G.mb i).nZ) :
    SeatsAre G P.oM P.oZ S L :=
  seatsAre_of P.id P.ix P.oM P.oZ P.sh hL.members hL.kept hL.mainFirst hL.maskFirst hnd S hsh hM hZ

section
variable {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12} {L : GroupLayout}

/-- **Of the group that the kind's law names.** -/
theorem seatsAre_gp (h : Good F a row D) (hm : Made p t a L D) (rad : ℕ → ℕ)
    (hnd : L.members.toList.Nodup) (S : Statement)
    (hsh : ∀ i : Fin D.mems.length, ∃ x, S.oracles[(D.mems.get i).id]? = some x ∧ x.shape = (D.mems.get i).sh) :
    SeatsAre (gpG h rad) (fun i => oM D.L i.val) (fun i => oZ D.L i.val) S L :=
  seatsAre_of (G := gpG h rad) (fun i => (D.mems.get i).id) (fun i => i.val) _ _ (fun i => (D.mems.get i).sh)
    (fun i => (hm.mem i).1) (fun w => by rw [← hm.lay]; exact h.kept w)
    (fun i h0 => by
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h.firstM i h0)
      rw [← hm.lay]
      show D.L.mainFirst.getD i.val none = some ((D.L.mainFirst.getD i.val none).getD 0)
      rw [hf]
      rfl)
    (fun i h0 => by
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 (h.firstZ i h0)
      rw [← hm.lay]
      show D.L.maskFirst.getD i.val none = some ((D.L.maskFirst.getD i.val none).getD 0)
      rw [hf]
      rfl)
    hnd S hsh (fun _ => rfl) (fun _ => rfl)

/-- At the plain data's own statement each member has its shape. -/
theorem shapes_made (hm : Made p t a L D) (i : Fin D.mems.length) :
    ∃ x, D.st.oracles[(D.mems.get i).id]? = some x ∧ x.shape = (D.mems.get i).sh :=
  (hm.mem i).2.oracle

/-- That group's seats are by numbers, with room, and apart. -/
theorem numbered_gp (h : Good F a row D) (rad : ℕ → ℕ) :
    (gpG h rad).Numbered (fun i => oM D.L i.val) (fun i => oZ D.L i.val) :=
  { pM := fun _ _ => rfl
    pZ := fun _ _ => rfl
    roomM := fun i => h.roomM i
    roomZ := fun i => h.roomZ i
    apartM := fun i j hij => h.apartM i j hij
    apartZ := fun i j hij => h.apartZ i j hij }

/-- **So the word of which the kind's law speaks has rows of zeros wherever no member has a real row.** -/
theorem rowsBlank_gp (h : Good F a row D) (hm : Made p t a L D) (rad : ℕ → ℕ)
    (hnd : L.members.toList.Nodup) (S : Statement) (G' : Group) (Fa : LayFacts S G' L)
    (hsh : ∀ i : Fin D.mems.length, ∃ x, S.oracles[(D.mems.get i).id]? = some x ∧ x.shape = (D.mems.get i).sh)
    (hk : L.k = (sg a).h + (sg a).g) (hh : L.h = (sg a).h)
    (yw : (gpG h rad).Words) : RowsBlank (sg a) S L ((gpG h rad).word yw) :=
  rowsBlank_word (gpG h rad) _ _ (numbered_gp h rad) S G' L Fa hk hh (seatsAre_gp h hm rad hnd S hsh) yw

end

end Johnson.RunOne.Law.RngSeats

#print axioms Johnson.RunOne.Law.RngSeats.find_at
#print axioms Johnson.RunOne.Law.RngSeats.seatsAre_of
#print axioms Johnson.RunOne.Law.RngSeats.seatsAre_of_lay
#print axioms Johnson.RunOne.Law.RngSeats.seatsAre_gp
#print axioms Johnson.RunOne.Law.RngSeats.numbered_gp
#print axioms Johnson.RunOne.Law.RngSeats.rowsBlank_gp
