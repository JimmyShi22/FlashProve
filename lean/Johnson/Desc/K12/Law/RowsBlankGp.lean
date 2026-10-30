-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RowsBlankGp.lean: what comes in front of the proximity test and the test's law
speak of one word: `RowsBlank` holds of the word of the law's own group. Statements and proofs.

`RowsBlank` is that of Johnson/Desc/K12/Law/TabWords.lean; the law's own group is `gpG`
(Johnson/Desc/K12/Law/FirstOkLaw.lean): the word y of `yOf` (Johnson/Desc/K12/Law/K12Lemma.lean) is
(gpG …).word of the members' written oracles. Public data and definitions: no view stands in it.
Main names:
  `find_of_nodup`: in a list of members without a double the layout finds a member at its own
    number.
  `numbered_gpG`: the group's seats are by numbers (`Gp.Numbered`), from the fields roomM, roomZ,
    apartM and apartZ of `Good`.
  `shapes_back`: the members' shapes at the statement S' behind the batching, where the plain data's
    statement D.st keeps the shapes of S''s messages (`ShapesKeep S' D.st`: D.st is S' where the
    first fold's mask had come: `ShapesKeep.refl`; where the fold brings its own mask D.st lies
    behind its entering: `recvP_keeps`, Johnson/Desc/K12/Law/OutK.lean).
  `seatsAre_gpG`: SeatsAre (gpG h rad) (oM D.L ·) (oZ D.L ·) S' L, from `Good` (kept, firstM,
    firstZ) and `Made` (lay, mem).
  `rowsBlank_gpG`: `Good`, `Made`, the group G' and the layout L of S', `GroupOk S' G'`, `ShapesKeep
    S' D.st`, L.k = a.h + (a.k − a.h) and L.h = a.h give RowsBlank (sg a) S' L ((gpG h rad).word
    yw), whatever the members' sent words yw.
  `shapesKeep_made`: `Made p t a L D` gives `ShapesKeep t.st D.st`, in both arms: where the record
    names the mask D.st is t.st; where the fold brings its own, D.st is what `recvP` returns from
    t's record, and the library's `stSent_old` serves (over `recvP_ok`).
  `rowsBlank_law`: `rowsBlank_gpG` at S' := t.st, with no premise on shapes left.
Every premise of `rowsBlank_law` is one that the law or `rIn_rows` has already: `Good` (`good_of_ok`
at the Boolean on the group); `Made` (`made_of` at the value of `gpOf`, at the record t behind the
batching); hG, hL and hOk (`combineAt_gives`); the two equations on L.
Limits: nothing is said on the members' own words, on the mask's word z, or on a view. No soundness
is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `layout_eq`, `layFacts`
(Johnson/Desc/Means/Layout.lean) and fields of `GroupOk`; `rowsBlank_word`
(Johnson/Desc/K12/Law/RowsBlankWord.lean), `recvP_ok` (Johnson/Desc/K12/Law/SwUnfold.lean);
`stSent_old` (OnBytes/Slice/BlkStLaws.lean), `ShapesKeep.refl` and the definition `ShapesKeep`
(OnBytes/Slice/BlkSeat.lean); fields of `Good`, `Made` and `Part1P`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.FirstOkLaw
import Johnson.Desc.K12.Law.RowsBlankWord

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Means
open H2K.First

/-- In a list of members without a double, the layout finds a member at its own number. -/
theorem find_of_nodup {L : GroupLayout} (hn : L.members.toList.Nodup) {i o : Nat}
    (h : L.members[i]? = some o) : L.find o = some i := by
  unfold GroupLayout.find
  rcases hm : L.members with ⟨l⟩
  rw [hm] at hn h
  have h' : l[i]? = some o := by simpa using h
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h'
  rw [List.idxOf?_toArray, List.idxOf?_eq_some_iff]
  refine ⟨hi, e, fun j hj hje => ?_⟩
  have hjl : j < l.length := lt_trans hj hi
  have : j = i := (List.Nodup.getElem_inj_iff hn).1
    (by simpa using (by simpa using hje : l[j] = o).trans e.symm)
  omega

variable {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain}

theorem numbered_gpG (h : Good F a row D) (rad : ℕ → ℕ) :
    (gpG h rad).Numbered (fun i => oM D.L i.val) fun i => oZ D.L i.val where
  pM := fun _ _ => rfl
  pZ := fun _ _ => rfl
  roomM := fun i => h.roomM i
  roomZ := fun i => h.roomZ i
  apartM := fun i j hij => h.apartM i j hij
  apartZ := fun i j hij => h.apartZ i j hij

/-- The members' shapes at a statement S' whose messages' shapes the plain data's statement keeps.
-/
theorem shapes_back {p : P12} {t : T12} {L : GroupLayout} (hm : Made p t a L D) (S' : Statement)
    (hs : ShapesKeep S' D.st) (ht : ∀ o ∈ L.members.toList, o < S'.oracles.size)
    (i : Fin D.mems.length) :
    ∃ x, S'.oracles[(D.mems.get i).id]? = some x ∧ x.shape = (D.mems.get i).sh := by
  have hmem : (D.mems.get i).id ∈ L.members.toList := by
    have := (hm.mem i).1
    rw [← Array.getElem?_toList] at this
    exact List.mem_of_getElem? this
  have hlt := ht _ hmem
  obtain ⟨x', hx', ex'⟩ := hs _ _ (Array.getElem?_eq_getElem hlt)
  obtain ⟨x, hx, ex⟩ := (hm.mem i).2.oracle
  rw [hx] at hx'
  obtain rfl := Option.some.inj hx'
  exact ⟨_, Array.getElem?_eq_getElem hlt, ex'.symm.trans ex⟩

/-- The seats of the law's own group are the layout's. -/
theorem seatsAre_gpG {p : P12} {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L
    D)
    (rad : ℕ → ℕ) (S' : Statement) (hn : L.members.toList.Nodup)
    (hsh : ∀ i : Fin D.mems.length,
      ∃ x, S'.oracles[(D.mems.get i).id]? = some x ∧ x.shape = (D.mems.get i).sh) :
    SeatsAre (gpG h rad) (fun i => oM D.L i.val) (fun i => oZ D.L i.val) S' L where
  at_ := fun i => by
    obtain ⟨x, hx, ex⟩ := hsh i
    have hL := hm.lay
    subst hL
    refine ⟨(D.mems.get i).id, i.val, find_of_nodup hn (hm.mem i).1, h.kept _, ?_, ?_, fun h0 => ?_,
      fun h0 => ?_⟩
    · unfold realRows
      rw [hx]
      show x.shape.rows Part.main = _
      rw [ex]
      rfl
    · unfold realRows
      rw [hx]
      show x.shape.rows Part.mask = _
      rw [ex]
      rfl
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstM i h0)
      unfold oM
      rw [hv]
      rfl
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstZ i h0)
      unfold oZ
      rw [hv]
      rfl

/-- RowsBlank of the word that the proximity test's law names: the word of the law's own group gpG,
whatever the
members' sent words. -/
theorem rowsBlank_gpG {p : P12} {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L
    D)
    (rad : ℕ → ℕ) (S' : Statement) (g : Nat) (G' : Group) (hG : S'.groups[g]? = some G')
    (hL : S'.layout g = some L) (hOk : GroupOk S' G') (hs : ShapesKeep S' D.st)
    (hk : L.k = a.h + (a.k - a.h)) (hh : L.h = a.h) (yw : (gpG h rad).Words) :
    RowsBlank (sg a) S' L ((gpG h rad).word yw) := by
  have hLm : L.members = G'.members := by
    have e := layout_eq S' g G' hG
    rw [hL] at e
    rw [Option.some.inj e]
    rfl
  exact rowsBlank_word (gpG h rad) _ _ (numbered_gpG h rad) S' G' L (layFacts hG hL hOk) hk hh
    (seatsAre_gpG h hm rad S' (by rw [hLm]; exact hOk.nodup)
      (shapes_back hm S' hs (by rw [hLm]; exact hOk.there))) yw

/-- What is sent keeps the elder messages, so their shapes. (The lines of the lemma of this name in
Johnson/Desc/K12/Law/OutK.lean; laid here so that this file's imports stay few.) -/
theorem stSent_keeps' (S : Statement) (sent : Array OracleNotice) : ShapesKeep S (stSent S sent) :=
    by
  intro o x hx
  have ho : o < S.oracles.size := by
    rcases Nat.lt_or_ge o S.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  exact ⟨x, by rw [stSent_old S _ o ho]; exact hx, rfl⟩

/-- The plain data's statement keeps the shapes of the record's messages: in both arms of the mask.
-/
theorem shapesKeep_made {p : P12} {t : T12} {L : GroupLayout} (hm : Made p t a L D) :
    ShapesKeep t.st D.st := by
  obtain ⟨cu, _, he⟩ := hm.ent
  unfold entered at he
  split at he
  · have e : t.st = D.st := congrArg (fun x => x.2.1) (Option.some.inj he)
    rw [← e]
    exact ShapesKeep.refl _
  · obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨id, _, he⟩ := Option.map_eq_some_iff.1 he
    have e : x.2.st = D.st := congrArg (fun x => x.2.1) he
    rw [← e]
    obtain ⟨ids, d1⟩ := x
    obtain ⟨lay, _, _, _, rfl⟩ := H2K.Sw.recvP_ok hx
    exact stSent_keeps' _ _

/-- RowsBlank of the word that the proximity test's law names, at the statement of the record t
behind the
batching: no premise on shapes is left. -/
theorem rowsBlank_law {p : P12} {t : T12} {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L
    D)
    (rad : ℕ → ℕ) (g : Nat) (G' : Group) (hG : t.st.groups[g]? = some G')
    (hL : t.st.layout g = some L) (hOk : GroupOk t.st G') (hk : L.k = a.h + (a.k - a.h))
    (hh : L.h = a.h) (yw : (gpG h rad).Words) : RowsBlank (sg a) t.st L ((gpG h rad).word yw) :=
  rowsBlank_gpG h hm rad t.st g G' hG hL hOk (shapesKeep_made hm) hk hh yw

end H2K.ClaimSays

#print axioms H2K.ClaimSays.seatsAre_gpG
#print axioms H2K.ClaimSays.rowsBlank_gpG
#print axioms H2K.ClaimSays.rowsBlank_law
