-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontAnswers.lean: WHEN THE CODE SWITCH's FRONT's READING OF THE CARRIED
ROWS ANSWERS (`K2.longFront … q = some seg`): AT EVERY POSITION q, FROM FACTS THAT NAME NO POSITION
AND NO STRING: the clause `all` of `FrontFits` (CarryAtRow.lean). The converse of LongText.lean's
and FrontCols.lean's inversions. Theorems. No text already in the library turns.

  `layRows_yes`, `layMember_yes`, `layMembers_yes`: the laying says yes where each column is empty
    or has a first row and fits the table.
  `ColFits L w nM nZ K H`: member w, with nM main and nZ mask symbols, fits the layout's tables of K
    and H rows.
  `keptOf_size`: the kept symbols are as many as the kept members' main symbols.
  `rowsAt_yes`: **two masks · every member has a column that fits · the kept symbols are
    s.keptRows many · the fresh mask has a column of 2 ^ h mask symbols ⊢ rowsAt says yes.**
  `Opens`: the front's book is there; every message that is opened has a place in it, that place's
    tree is there, and the front's statement has the message.
  `front_answers`: **Opens · two masks · each member's shape's rows fit the layout (ColFits) · the
    kept members' main rows add up to rows.keptRows · the fresh mask's shape has 2 ^ h mask rows ⊢
    ∀ q, ∃ seg, K2.longFront p t fx orc q = some seg.**
Limits. The premises are on the verifier's state (its book) and the front's statement and layout:
not paid here. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.FrontCols
import Johnson.Desc.First.Link.Law.LongMasks
import Johnson.Top.H0.Tw.K2.RowsMadeAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (Tables layFrom layRows layMember layMembers rowsAt)
open _root_.Tw.K2 (switchNotices)

/-! ## 1 The laying says yes -/

theorem layRows_yes (table : Array E) (first : Option ℕ) (col : Array E)
    (h : col.size = 0 ∨ ∃ f, first = some f ∧ f + col.size ≤ table.size) :
    ∃ t', layRows table first col = some t' := by
  unfold layRows
  cases e : col.toList with
  | nil => exact ⟨table, rfl⟩
  | cons x xs =>
    have hs : col.size = (x :: xs).length := by rw [← e, Array.length_toList]
    rcases h with h | ⟨f, rfl, hf⟩
    · rw [hs] at h
      exact nomatch h
    · rw [hs] at hf
      exact ⟨_, if_pos hf⟩

/-- Member w, with nM main and nZ mask symbols, fits the layout's tables of K and H rows. -/
def ColFits (L : GroupLayout) (w nM nZ K H : ℕ) : Prop :=
  (nZ = 0 ∨ ∃ f, L.maskFirst.getD w none = some f ∧ f + nZ ≤ H) ∧
    (L.kept.getD w false = true ∨ nM = 0 ∨ ∃ f, L.mainFirst.getD w none = some f ∧ f + nM ≤ K)

theorem layMember_yes {L : GroupLayout} {w : ℕ} {col : Column} {t : Tables}
    (h : ColFits L w col.main.size col.mask.size t.main.size t.mask.size) :
    ∃ t', layMember L w col t = some t' := by
  obtain ⟨mask, hm⟩ := layRows_yes t.mask (L.maskFirst.getD w none) col.mask h.1
  unfold layMember
  rw [hm]
  by_cases hk : L.kept.getD w false = true
  · exact ⟨_, if_pos hk⟩
  · obtain ⟨main, hn⟩ := layRows_yes t.main (L.mainFirst.getD w none) col.main
      (h.2.resolve_left hk)
    refine ⟨⟨main, mask, t.kept⟩, ?_⟩
    show (if L.kept.getD w false = true then _ else _) = _
    rw [if_neg hk, hn]
    rfl

theorem layMembers_yes (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t : Tables),
      (∀ w ∈ ws, ∃ c, colAt opened i w = some c ∧
        ColFits L w c.main.size c.mask.size t.main.size t.mask.size) →
      ∃ t', layMembers L opened i ws t = some t'
  | [], t, _ => ⟨t, rfl⟩
  | w :: ws, t, h => by
    obtain ⟨c, hc, hf⟩ := h w List.mem_cons_self
    obtain ⟨t₁, h1⟩ := layMember_yes hf
    obtain ⟨z1, z2⟩ := layMember_sizes h1
    obtain ⟨t', h2⟩ := layMembers_yes L opened i ws t₁ fun w' hw' => by
      rw [z1, z2]
      exact h w' (List.mem_cons_of_mem _ hw')
    refine ⟨t', ?_⟩
    unfold layMembers
    have hc' : ((opened[w]?).bind (·[i]?)) = some c := hc
    rw [hc']
    show (layMember L w c t).bind _ = _
    rw [h1]
    exact h2

/-- The kept members' main symbols, counted. -/
def keptCount (L : GroupLayout) (nM : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: ws => (if L.kept.getD w false then nM w else 0) + keptCount L nM ws

theorem keptOf_size (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) (nM : ℕ → ℕ) :
    ∀ ws : List ℕ, (∀ w ∈ ws, ∃ c, colAt opened i w = some c ∧ c.main.size = nM w) →
      (keptOf L opened i ws).size = keptCount L nM ws
  | [], _ => rfl
  | w :: ws, h => by
    obtain ⟨c, hc, hn⟩ := h w List.mem_cons_self
    rw [keptOf_cons, Array.size_append, keptOf_size L opened i nM ws fun w' hw' =>
      h w' (List.mem_cons_of_mem _ hw'), hc]
    show _ = (if L.kept.getD w false then nM w else 0) + _
    congr 1
    by_cases hk : L.kept.getD w false = true
    · rw [if_pos hk, if_pos hk]
      exact hn
    · rw [if_neg hk, if_neg hk]
      rfl

/-- **rowsAt SAYS YES.** -/
theorem rowsAt_yes {s : SingleRows} (hm : s.masks = 2) {opened : Array (Array Column)} {i : ℕ}
    (nM : ℕ → ℕ)
    (hc : ∀ w ∈ List.range s.layout.members.size, ∃ c, colAt opened i w = some c ∧
      c.main.size = nM w ∧
      ColFits s.layout w c.main.size c.mask.size (2 ^ s.layout.k) (2 ^ s.layout.h))
    (hk : keptCount s.layout nM (List.range s.layout.members.size) = s.keptRows)
    (hf : ∃ c, colAt opened i s.layout.members.size = some c ∧ c.mask.size = 2 ^ s.layout.h) :
    ∃ seg, rowsAt s opened #[] i = some seg := by
  obtain ⟨t, ht⟩ := layMembers_yes s.layout opened i (List.range s.layout.members.size)
    (blankTables s.layout) fun w hw => by
      obtain ⟨c, h1, _, h3⟩ := hc w hw
      refine ⟨c, h1, ?_⟩
      show ColFits s.layout w c.main.size c.mask.size (Array.replicate _ zeroE).size
        (Array.replicate _ zeroE).size
      rw [Array.size_replicate, Array.size_replicate]
      exact h3
  have hks : t.kept.size = s.keptRows := by
    rw [kept_laid _ _ _ _ _ _ ht, Array.size_append, keptOf_size s.layout opened i nM _
      fun w hw => by
        obtain ⟨c, h1, h2, _⟩ := hc w hw
        exact ⟨c, h1, h2⟩, hk]
    exact Nat.zero_add _
  obtain ⟨c, hc1, hc2⟩ := hf
  unfold rowsAt
  dsimp only
  have ht' : layMembers s.layout opened i (List.range s.layout.members.size)
      ⟨Array.replicate (2 ^ s.layout.k) zeroE, Array.replicate (2 ^ s.layout.h) zeroE, #[]⟩ =
      some t := ht
  have hc1' : ((opened[s.layout.members.size]?).bind (·[i]?)) = some c := hc1
  rw [ht']
  simp [hks, hm, hc1', hc2]

/-! ## 2 The front answers -/

/-- The front's book is there, and every message that is opened can be read in it. -/
structure Opens (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front) (B : TreeBook) :
    Prop where
  book : First.K2.bookAt (First.K2.par9 p).firstTree fx.st t.book t.roots
    (switchNotices fx.T fx.others) = some B
  place : ∀ o ∈ (singleRowsOracles fx.f.rows).toList, ∃ pl tr xo, B.place[o]? = some pl ∧
    B.trees[pl.1]? = some tr ∧ (First.K2.skelOf fx).oracles[o]? = some xo

variable {p : First.K2.P2} {t : First.S} {fx : _root_.Tw.K2.Front} {B : TreeBook}

theorem opens_places (O : Opens p t fx B) :
    ∃ places, ((singleRowsOracles fx.f.rows).mapM fun o => B.place[o]?) = some places := by
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (_root_.Tw.K2.mapM_some (fun o => B.place[o]?)
    (singleRowsOracles fx.f.rows).toList fun o ho => by
      obtain ⟨pl, _, _, h, _⟩ := O.place o ho
      show (B.place[o]?).isSome = true
      rw [h]
      rfl)
  exact ⟨r.toArray, by rw [hr]; rfl⟩

/-- Every opened message has its column, at every position. -/
theorem opens_col (O : Opens p t fx B) (orc : ℕ → ℕ → List UInt64) {places : Array (ℕ × ℕ)}
    (hP : ((singleRowsOracles fx.f.rows).mapM fun o => B.place[o]?) = some places) (q : ℕ) {w : ℕ}
    (hw : w < (singleRowsOracles fx.f.rows).size) :
    ∃ c, colAt (frontCols p fx orc B places q) 0 w = some c := by
  obtain ⟨zs, zp⟩ := OnBytes.Slice.array_mapM_inv _ _ _ hP
  have hwp : w < places.size := by rw [zs]; exact hw
  have hwz : w < ((singleRowsOracles fx.f.rows).zip places).size := by
    rw [Array.size_zip]
    omega
  obtain ⟨pl, tr, xo, h1, h2, h3⟩ := O.place (singleRowsOracles fx.f.rows)[w]
    (Array.getElem_mem_toList hw)
  have hpl := zp w hw
  rw [Array.getElem?_eq_getElem hwp, h1] at hpl
  have epl : places[w] = pl := (Option.some.inj hpl).symm
  unfold colAt frontCols First.K2.openedOne
  rw [Array.getElem?_map, Array.getElem?_eq_getElem hwz, Array.getElem_zip, epl]
  unfold First.K2.colOne
  simp [h2, h3]

/-- **THE FRONT ANSWERS AT EVERY POSITION.** -/
theorem front_answers (O : Opens p t fx B) (orc : ℕ → ℕ → List UInt64)
    (hm : fx.f.rows.masks = 2)
    (hfit : ∀ w (hw : w < fx.f.rows.layout.members.size), ColFits fx.f.rows.layout w
      ((First.K2.skelOf fx).oracles.getD fx.f.rows.layout.members[w] default).shape.mainRows
      ((First.K2.skelOf fx).oracles.getD fx.f.rows.layout.members[w] default).shape.maskRows
      (2 ^ fx.f.rows.layout.k) (2 ^ fx.f.rows.layout.h))
    (hk : keptCount fx.f.rows.layout
      (fun w => ((First.K2.skelOf fx).oracles.getD (fx.f.rows.layout.members.getD w 0)
        default).shape.mainRows) (List.range fx.f.rows.layout.members.size) = fx.f.rows.keptRows)
    (hfr : ((First.K2.skelOf fx).oracles.getD fx.f.rows.fresh default).shape.maskRows =
      2 ^ fx.f.rows.layout.h) (q : ℕ) :
    ∃ seg, First.K2.longFront p t fx orc q = some seg := by
  obtain ⟨places, hP⟩ := opens_places O
  have hso : singleRowsOracles fx.f.rows =
      fx.f.rows.layout.members.push fx.f.rows.fresh := by
    unfold singleRowsOracles
    simp [hm]
  have hsz : (singleRowsOracles fx.f.rows).size = fx.f.rows.layout.members.size + 1 := by
    rw [hso, Array.size_push]
  obtain ⟨seg, hs⟩ := rowsAt_yes (s := fx.f.rows) hm
    (opened := frontCols p fx orc B places q) (i := 0)
    (fun w => ((First.K2.skelOf fx).oracles.getD (fx.f.rows.layout.members.getD w 0)
      default).shape.mainRows)
    (fun w hw => by
      have hlt := List.mem_range.1 hw
      have hw' : w < (singleRowsOracles fx.f.rows).size := by omega
      obtain ⟨c, hc⟩ := opens_col O orc hP q hw'
      obtain ⟨_, _, c3, c4⟩ := front_col O.book hP hw' hc
      have eo : (singleRowsOracles fx.f.rows)[w] = fx.f.rows.layout.members[w] := by
        simp only [hso]
        exact Array.getElem_push_lt hlt
      rw [eo] at c3 c4
      refine ⟨c, hc, ?_, ?_⟩
      · have eg : fx.f.rows.layout.members.getD w 0 = fx.f.rows.layout.members[w] := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
          rfl
        show c.main.size = ((First.K2.skelOf fx).oracles.getD
          (fx.f.rows.layout.members.getD w 0) default).shape.mainRows
        rw [c3, eg]
      · rw [c3, c4]
        exact hfit w hlt) hk
    (by
      have hw' : fx.f.rows.layout.members.size < (singleRowsOracles fx.f.rows).size := by omega
      obtain ⟨c, hc⟩ := opens_col O orc hP q hw'
      obtain ⟨_, _, _, c4⟩ := front_col O.book hP hw' hc
      have eo : (singleRowsOracles fx.f.rows)[fx.f.rows.layout.members.size] =
          fx.f.rows.fresh := by
        simp only [hso]
        exact Array.getElem_push_eq
      rw [eo] at c4
      exact ⟨c, hc, c4.trans hfr⟩)
  refine ⟨seg, ?_⟩
  unfold First.K2.longFront
  rw [O.book]
  show (((singleRowsOracles fx.f.rows).mapM fun o => B.place[o]?).bind _) = _
  rw [hP]
  exact hs

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.opens_places
#print axioms VerifiableInference.Desc.LinkJoin.opens_col
#print axioms VerifiableInference.Desc.LinkJoin.front_answers
#print axioms VerifiableInference.Desc.LinkJoin.layMembers_yes
#print axioms VerifiableInference.Desc.LinkJoin.keptOf_size
#print axioms VerifiableInference.Desc.LinkJoin.rowsAt_yes
