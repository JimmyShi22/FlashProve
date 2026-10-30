-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ReadsRoomAtAny.lean: WHAT AN ACCEPT OF THE PUBLIC TESTS ON THE SEGMENTS'
STRUCTURES (buildLinksH, OnBytes/Model/StagesLinks.lean) SAYS OF EVERY SEGMENT's VECTOR OF READS:
the request's layout has an array named "U3" at that segment, with the rows and columns of the
plan's array. The library has this at the LAST segment (`reads_named_of_built`,
Johnson/Desc/Kinds/Law/ReadsRoomOfBuilt.lean): its stones are general and are called here
(`Decl`, `declareOwn_reads`, `heldAgainst_at`, `linkHeld_at`); new is the lift through the later
readers. General in the segments' structures: no scope, no public part. Statements with their
proofs; no routine is evaluated.

How. A later reader turns an earlier segment's declaration by keptUpTo alone, which writes LIVES
into arrays of the first moment: an array's name, rows and columns stay.

  `DeclU mo R K`   an array named "U3" is declared at some moment, with R rows and K columns
  `KeepsU D D'`   what D declares under "U3", D' declares
  `keptUpTo_keepsU`, `foreign_frames`   the two routines that touch an earlier declaration
  `declareLinks_atAny`   every segment in the declarations of all
  `reads_room_of_built`   **MAIN**

What is not claimed. Under which number the name stands in the segment's list of arrays
(ReadsNameOnly.lean, this folder, has the converse). Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.ReadsRoomOfBuilt
import Johnson.Road.K4.Names.DeclaredNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.Only

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open OnBytes.TieK (ok_of_bind ok_of_jp forIn_keeps)
open VerifiableInference.Desc.Kinds.Head.Law.Built (Decl declareOwn_reads heldAgainst_at
  linkHeld_at)

/-- An array named "U3" is declared at some moment, with R rows and K columns. -/
def DeclU (mo : Array (Array FrameArray)) (R K : ℕ) : Prop :=
  ∃ a, Decl mo a ∧ a.name = "U3" ∧ a.rows = R ∧ a.columns = K

/-- What D declares under "U3", D' declares. -/
def KeepsU (D D' : FrameLink) : Prop := ∀ R K, DeclU D.moment R K → DeclU D'.moment R K

theorem keptUpTo_keepsU {D D' : FrameLink} {name : String} {life : ℕ}
    (h : keptUpTo D name life = .ok D') : KeepsU D D' := by
  unfold keptUpTo at h
  dsimp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    rintro R K ⟨a, ⟨j, M, hj, hm⟩, n1, n2, n3⟩
    have hlt : j < D.moment.size := (Array.getElem?_eq_some_iff.1 hj).1
    by_cases h0 : j = 0
    · subst h0
      have eM : D.moment.getD 0 #[] = M := by
        rw [Array.getD_eq_getD_getElem?, hj]
        rfl
      refine ⟨if a.name == name then { a with life := max a.life life } else a,
        ⟨0, M.map fun a => if a.name == name then { a with life := max a.life life } else a,
          ?_, ?_⟩, ?_, ?_, ?_⟩
      · show (D.moment.setIfInBounds 0 _)[0]? = _
        rw [Array.getElem?_setIfInBounds, if_pos rfl, if_pos hlt, eM]
      · rw [Array.toList_map]
        exact List.mem_map_of_mem hm
      · split <;> exact n1
      · split <;> exact n2
      · split <;> exact n3
    · refine ⟨a, ⟨j, M, ?_, hm⟩, n1, n2, n3⟩
      show (D.moment.setIfInBounds 0 _)[j]? = some M
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm h0)]
      exact hj
  · cases h

/-- Naming an array that an earlier segment sent keeps the number of the declarations and what each
declares under "U3". -/
theorem foreign_frames {links : Array LinkH} {NGr : ℕ} {p4 : Bool} {l : ℕ} {X : LinkH}
    {s s' : Array (ℕ × String) × Array FrameLink} {tree : ℕ} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    s'.2.size = s.2.size ∧ ∀ (j : ℕ) (D : FrameLink), s.2[j]? = some D →
      ∃ D', s'.2[j]? = some D' ∧ KeepsU D D' := by
  unfold foreign at h
  dsimp only at h
  split at h
  · rename_i owner _
    replace h := exc_guard h
    split at h
    · split at h
      · replace h := exc_guard h
        split at h
        · split at h
          · split at h
            · replace h := exc_guard h
              obtain ⟨arrayOf, _, h⟩ := exc_bind h
              split at h
              · rename_i D0 hD0
                obtain ⟨D1, hk, h⟩ := exc_bind h
                obtain rfl := Except.ok.inj h
                refine ⟨by simp, fun j D hj => ?_⟩
                have hlt : j < s.2.size := (Array.getElem?_eq_some_iff.1 hj).1
                by_cases hc : layersLink p4 owner = j
                · subst hc
                  obtain rfl : D0 = D := Option.some.inj (hD0.symm.trans hj)
                  refine ⟨D1, ?_, keptUpTo_keepsU hk⟩
                  show (s.2.setIfInBounds _ D1)[_]? = some D1
                  rw [Array.getElem?_setIfInBounds, if_pos rfl, if_pos hlt]
                · refine ⟨D, ?_, fun _ _ g => g⟩
                  show (s.2.setIfInBounds _ D1)[j]? = some D
                  rw [Array.getElem?_setIfInBounds_ne hc]
                  exact hj
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Every segment in the declarations of all**: what its own declaration declares under "U3" is
declared at its number behind all later readers. -/
theorem declareLinks_atAny {links : Array LinkH} {NGr : ℕ} {p4 : Bool}
    {r : Array LinkH × Array FrameLink} (h : declareLinks links NGr p4 = .ok r) {n : ℕ}
    {Y : LinkH} (hY : links[n]? = some Y) :
    ∃ (d : Declaring) (D : FrameLink), declareOwn Y n = .ok d ∧ r.2[n]? = some D ∧
      ∀ R K, DeclU d.moment R K → DeclU D.moment R K := by
  unfold declareLinks at h
  obtain ⟨st, hr, h⟩ := ok_of_bind h
  obtain ⟨declared, named⟩ := st
  obtain rfl : (named, declared) = r := Except.ok.inj h
  have K := forIn_keeps _ links.toList.zipIdx
    (fun pr (s : MProd (Array FrameLink) (Array LinkH)) =>
      s.fst.size = pr.length ∧ ∀ (j : ℕ) (X : LinkH) (l : ℕ), pr[j]? = some (X, l) →
        ∃ (d : Declaring) (D : FrameLink), declareOwn X l = .ok d ∧ s.fst[j]? = some D ∧
          ∀ R K, DeclU d.moment R K → DeclU D.moment R K) ?_
    links.toList.zipIdx [] _ _ rfl ⟨rfl, fun j X l c => by simp at c⟩ hr
  · exact K.2 n Y n (by
      rw [List.getElem?_zipIdx, Array.getElem?_toList, hY]
      simp)
  · intro pr a rest e s s' hI hs
    obtain ⟨i1, i2⟩ := hI
    obtain ⟨X, l⟩ := a
    obtain ⟨d, hd, hs⟩ := ok_of_bind hs
    obtain ⟨s2, h2, hs⟩ := ok_of_bind hs
    obtain ⟨-, hs⟩ := ok_of_jp hs
    have J := forIn_keeps _ (zipT X.tl.ix.FT.toList X.tl.plFor.toList)
      (fun _ (x : Array (ℕ × String) × Array FrameLink) =>
        x.2.size = s.fst.size ∧ ∀ (j : ℕ) (D : FrameLink), s.fst[j]? = some D →
          ∃ D', x.2[j]? = some D' ∧ KeepsU D D')
      ?_ (zipT X.tl.ix.FT.toList X.tl.plFor.toList) [] _ _ rfl
      ⟨rfl, fun j D hj => ⟨D, hj, fun _ _ g => g⟩⟩ h2
    · obtain ⟨j1, j2⟩ := J
      refine ⟨_, (Except.ok.inj hs).symm, ?_, ?_⟩
      · show (s2.2.push _).size = _
        simp [j1, i1]
      · intro j X' l' hj
        by_cases hc : j < pr.length
        · rw [List.getElem?_append_left hc] at hj
          obtain ⟨d', D, a1, a2, a3⟩ := i2 j X' l' hj
          obtain ⟨D', b1, b2⟩ := j2 j D a2
          refine ⟨d', D', a1, ?_, fun R K g => b2 R K (a3 R K g)⟩
          show (s2.2.push _)[j]? = some D'
          rw [Array.getElem?_push_lt (by rw [j1, i1]; exact hc), ← b1,
            Array.getElem?_eq_getElem (by rw [j1, i1]; exact hc)]
        · have hj' : j = pr.length := by
            have h6 := (List.getElem?_eq_some_iff.1 hj).1
            simp at h6
            omega
          subst hj'
          obtain ⟨rfl, rfl⟩ : X = X' ∧ l = l' := by simpa using hj
          refine ⟨d, { name := X.name, moment := d.moment }, hd, ?_, fun _ _ g => g⟩
          show (s2.2.push _)[pr.length]? = _
          rw [← i1, ← j1, Array.getElem?_push_size]
    · intro pr2 a2 rest2 e2 x x' hJ hx
      obtain ⟨tree, pl⟩ := a2
      obtain ⟨y, hy, hx⟩ := ok_of_bind hx
      obtain ⟨f1, f2⟩ := foreign_frames hy
      refine ⟨y, (Except.ok.inj hx).symm, f1.trans hJ.1, fun j D hj => ?_⟩
      obtain ⟨D1, c1, c2⟩ := hJ.2 j D hj
      obtain ⟨D2, c3, c4⟩ := f2 j D1 c1
      exact ⟨D2, c3, fun R K g => c4 R K (c2 R K g)⟩

/-- **BEHIND AN ACCEPT OF THE PUBLIC TESTS ON THE SEGMENTS' STRUCTURES, AT EVERY SEGMENT: the given
layout has an array named "U3" there, with the rows and columns of the plan's array of the third
vector.** -/
theorem reads_room_of_built {l₀ : Array LinkH} {NGr : ℕ} {p4 : Bool} {ws : OnBytes.Model.WsLay}
    {first : Params.First} {B : LinksH} (hB : buildLinksH l₀ NGr p4 ws first = .ok B) {n t : ℕ}
    {Y : LinkH} (hY : l₀[n]? = some Y) (hU : Y.tl.ix.U.getD 2 none = some t) :
    ∃ tr A, Y.Fp.trees[t]? = some tr ∧ OnBytes.reqArray first.layout n "U3" = some A ∧
      A.sizeI = tr.R ∧ A.sizeC = tr.K := by
  unfold buildLinksH at hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨-, -, hB⟩ := ok_of_bind hB
  obtain ⟨⟨links', declared⟩, hd, hB⟩ := ok_of_bind hB
  obtain ⟨u, hh, hB⟩ := ok_of_bind hB
  cases u
  obtain ⟨d, D, a1, a2, a3⟩ := declareLinks_atAny hd hY
  obtain ⟨_, tr, m, g2, g3⟩ := declareOwn_reads a1 hU
  obtain ⟨a, b1, n1, n2, n3⟩ := a3 tr.R tr.K ⟨_, g3, rfl, rfl, rfl⟩
  obtain ⟨L, arrays, _, b2, b3⟩ := heldAgainst_at hh a2
  obtain ⟨A, c1, c2, c3⟩ := linkHeld_at b3 b1
  refine ⟨tr, A, g2, ?_, c2.trans n2, c3.trans n3⟩
  unfold OnBytes.reqArray
  rw [b2]
  rw [n1] at c1
  exact c1

end VerifiableInference.Desc.K1.Only

#print axioms VerifiableInference.Desc.K1.Only.keptUpTo_keepsU
#print axioms VerifiableInference.Desc.K1.Only.foreign_frames
#print axioms VerifiableInference.Desc.K1.Only.declareLinks_atAny
#print axioms VerifiableInference.Desc.K1.Only.reads_room_of_built
