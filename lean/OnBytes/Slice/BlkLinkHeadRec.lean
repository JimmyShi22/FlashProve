-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkHeadRec.lean: the link's steps and the batching after them, as one run, from
`LinkRanR`.

OnBytes/Slice/BlkLinkHead.lean puts together what a run of the link's steps has done and what a run
of the batching has done, from `LinkRan`. This file says the same again from `LinkRanR`
(OnBytes/Slice/BlkLinkRanRec.lean), where the group holds the rows of the two records too. All rows
that are batched meet the conditions of the laws on batching, are plain in the sense of `PlainRow`
(no tensor with a written-out factor, no whole vector that is not plain; not the rows' kind), and
have no term on a mask table. The row that the batching returns is given entry by entry, in any
commutative ring under a reading of the program's field elements, and so is what the two runs leave
of the codes, the book, the counts and the opened columns.

Main definition: `LinkDataR.rowsR`, the rows that are batched, in their order: the first table's
record's rows, the copy's, the equality row, the two sample rows, the rows of the first table's
draws, those of the copy's.
Main theorems.
 `LinkRanR.fits`, `LinkRanR.plain`, `LinkRanR.mainOnly`   on all rows that are batched.
 `LinkRanR.runRows_eq`   the proximity test takes in `LinkDataR.rowsR`.
 `LinkRanR.bat_input`    the group, the layout and the combination that the batching finds.
 `LinkRanR.bat_keeps`    the codes, the book, the counts and the opened columns after the two runs.
 `LinkRanR.bat_target`, `LinkRanR.bat_main`, `LinkRanR.bat_mask`   the returned row, entry by entry.
 `LinkRanR.bat_plain`    the returned row is a plain form on the group's main table.
Not claimed. What the rows' coefficients are (OnBytes/Slice/BlkLink.lean; for a record's rows
BlkRecRow.lean, BlkLinkRec.lean). Nothing on soundness.

-/
import OnBytes.Slice.BlkLinkBatRec
import OnBytes.Slice.BlkLinkHead
import OnBytes.Slice.BlkLinkRanRec
import OnBytes.Slice.BlkRecRow

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-- Each entry of the list that a loop which may fail returns is the value at an entry of the list
that it runs through. -/
theorem mapM_eachR {α β : Type} (f : α → Option β) : ∀ (l : List α) (l' : List β),
    l.mapM f = some l' → ∀ r ∈ l', ∃ a ∈ l, f a = some r
  | [], l', h, r, hr => by
    rw [List.mapM_nil] at h
    obtain rfl := Option.some.inj h
    cases hr
  | a :: l, l', h, r, hr => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨a', ha', h'⟩ := mapM_eachR f l bs hbs r hr
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

/-- Each row of a key's record is the row of a seed and a number. -/
theorem recRowsR_each (S : FoldeqShape) (key : TableKey) (eqGamma : Array E) (u : FoldedRow)
    (rows : List Row) (h : recRowsR S key eqGamma u = some rows) :
    ∀ r ∈ rows, ∃ seed i, foldeqRecordRow S seed key.record i eqGamma u = some r := fun r hr => by
  obtain ⟨a, _, ha⟩ := mapM_eachR _ _ _ h r hr
  exact ⟨a.1, a.2, ha⟩

/-- The rows of a key's record are plain rows by kind. -/
theorem recRowsR_kind (S : FoldeqShape) (key : TableKey) (eqGamma : Array E) (u : FoldedRow)
    (rows : List Row) (h : recRowsR S key eqGamma u = some rows) :
    ∀ r ∈ rows, r.kind = .plain := fun r hr => by
  obtain ⟨seed, i, h3⟩ := recRowsR_each S key eqGamma u rows h r hr
  exact recRow_kind _ _ _ _ _ _ _ h3

/-- The rows that are batched after the link's steps, in their order. -/
def LinkDataR.rowsR (D : LinkDataR) : List Row :=
  D.rec0 ++ (D.rec1 ++ D.rE :: { D.row0 with target := D.y0 } :: { D.row1 with target := D.y1 } ::
    (D.rows0 ++ D.rows1))

/-- A row that is batched is of one of seven makes. -/
theorem LinkDataR.mem_rowsR {D : LinkDataR} {r : Row} (h : r ∈ D.rowsR) :
    r ∈ D.rec0 ∨ r ∈ D.rec1 ∨ r = D.rE ∨ r = { D.row0 with target := D.y0 } ∨
      r = { D.row1 with target := D.y1 } ∨ r ∈ D.rows0 ∨ r ∈ D.rows1 := by
  simpa only [LinkDataR.rowsR, List.mem_append, List.mem_cons] using h

section
variable {S : LinkShape} {first further : TableKey} {c c1 c2 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D)

include hR

/-- A folded row's oracle message has at least one row. -/
theorem LinkRanR.rows_pos : 0 < S.rows := by
  have h := hR.ok
  unfold linkOk Params.LinkShape.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

/-- The point of the seed has as many coordinates as the cube of a folded row's oracle message. -/
theorem LinkRanR.seed_length :
    ((D.r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits).length =
      (Send.cube c.st.codes (rowShape S)).bits := by
  have h := congrArg List.length hR.factor
  rw [List.length_drop, List.length_singleton] at h
  rw [List.length_take]
  omega

/-- All rows that are batched meet the conditions of the laws on batching. -/
theorem LinkRanR.fits : ∀ r ∈ D.rowsR, RowFits c1.st r := by
  have hpos := hR.rows_pos
  have hz := Nat.le_of_eq (hR.seed_length).symm
  -- a sample row
  have hsmp : ∀ (b : Bool) (row : Row), Send.form c.st.codes (rowShape S)
      (c.st.oracles.size + b.toNat)
      ⟨(D.r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits, D.beta⟩ 0 =
        some row → RowFits c1.st row := by
    intro b row hf
    refine rowFits_form _ _ _ _ _ _ hf _ hz fun part hp => ?_
    cases part
    · rw [hR.st, linkStR, (linkSt_tables S c.st _ _ _ _ _ _ b).2.1]
      show ceilLog2 S.rows ≤ (Send.cube c.st.codes (rowShape S)).mainBits
      have hm : (Send.cube c.st.codes (rowShape S)).hasMain = true := hp
      rw [cube_mainBits_eq, if_pos hm, cube_mainRowBits_eq, if_pos hm]
      exact Nat.le_add_right _ _
    · cases hp
  intro r hr
  rcases LinkDataR.mem_rowsR hr with hr | hr | rfl | rfl | rfl | hr | hr
  · exact rowFits_of_checked (hR.checked _ (by simp [hr]))
  · exact rowFits_of_checked (hR.checked _ (by simp [hr]))
  · exact rowFits_of_checked (hR.checked _ List.mem_cons_self)
  · exact rowFits_target _ _ (hsmp false _ hR.form0) _
  · exact rowFits_target _ _ (hsmp true _ hR.form1) _
  · exact rowFits_of_checked (hR.checked _ (by simp [hr]))
  · exact rowFits_of_checked (hR.checked _ (by simp [hr]))

/-- The same in the statement after the steps, written out. -/
theorem LinkRanR.fitsSt : ∀ r ∈ D.rowsR, RowFits (linkStR S c.st D.places
    { D.row0 with target := D.y0 } { D.row1 with target := D.y1 } D.rec0 D.rec1 D.rows0 D.rows1
    D.rE) r := fun r hr => hR.st ▸ hR.fits r hr

/-- All rows that are batched are plain in the sense of `PlainRow`. -/
theorem LinkRanR.plain : ∀ r ∈ D.rowsR, PlainRow r := by
  intro r hr
  rcases LinkDataR.mem_rowsR hr with hr | hr | rfl | rfl | rfl | hr | hr
  · obtain ⟨seed, i, h3⟩ := recRowsR_each _ _ _ _ _ hR.rec0 r hr
    exact plainRow_of_terms _ (recRow_plain _ _ _ _ _ _ _ h3)
  · obtain ⟨seed, i, h3⟩ := recRowsR_each _ _ _ _ _ hR.rec1 r hr
    exact plainRow_of_terms _ (recRow_plain _ _ _ _ _ _ _ h3)
  · exact plainRow_of_terms _ (eqRow_plain _ _ _ _ _ _ hR.eqRow)
  · exact (plainRow_form _ _ _ _ _ D.row0 hR.form0 : PlainRow D.row0)
  · exact (plainRow_form _ _ _ _ _ D.row1 hR.form1 : PlainRow D.row1)
  · obtain ⟨a, y, h3⟩ := columnRows_each _ _ _ _ _ _ _ _ hR.rows0 r hr
    exact plainRow_of_terms _ (colRow_plain _ _ _ _ _ h3)
  · obtain ⟨a, y, h3⟩ := columnRows_each _ _ _ _ _ _ _ _ hR.rows1 r hr
    exact plainRow_of_terms _ (colRow_plain _ _ _ _ _ h3)

/-- No row that is batched has a term on a mask table. Of a row's single entries, which a record's
row has, nothing is said here. -/
theorem LinkRanR.mainOnly : ∀ r ∈ D.rowsR, ∀ t ∈ r.terms.toList, t.part = .main := by
  -- a sample row: a folded row's oracle message has no mask rows
  have hsmp : ∀ (o : Nat) (row : Row), Send.form c.st.codes (rowShape S) o
      ⟨(D.r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits, D.beta⟩ 0 =
        some row → ∀ t ∈ row.terms.toList, t.part = .main := by
    intro o row hf t ht
    rw [(form_parts _ _ _ _ _ _ hf).1, List.mem_append] at ht
    rcases ht with ht | ht
    · split at ht
      · rw [List.mem_singleton.1 ht]
      · cases ht
    · have hm : (Send.cube c.st.codes (rowShape S)).hasMask = false := rfl
      rw [hm] at ht
      cases ht
  intro r hr
  rcases LinkDataR.mem_rowsR hr with hr | hr | rfl | rfl | rfl | hr | hr
  · obtain ⟨seed, i, h3⟩ := recRowsR_each _ _ _ _ _ hR.rec0 r hr
    exact recRow_main _ _ _ _ _ _ _ h3
  · obtain ⟨seed, i, h3⟩ := recRowsR_each _ _ _ _ _ hR.rec1 r hr
    exact recRow_main _ _ _ _ _ _ _ h3
  · exact eqRow_main _ _ _ _ _ _ hR.eqRow
  · exact hsmp _ D.row0 hR.form0
  · exact hsmp _ D.row1 hR.form1
  · obtain ⟨a, y, h3⟩ := columnRows_each _ _ _ _ _ _ _ _ hR.rows0 r hr
    exact colRow_main _ _ _ _ _ h3
  · obtain ⟨a, y, h3⟩ := columnRows_each _ _ _ _ _ _ _ _ hR.rows1 r hr
    exact colRow_main _ _ _ _ _ h3

/-- The link's steps change no code. -/
theorem LinkRanR.codes : c1.st.codes = c.st.codes := by
  rw [hR.st]
  exact linkSt_codes _ _ _ _ _ _ _ _

/-- The opened columns that the link's steps leave were among those that they found. -/
theorem LinkRanR.opened_sub : ∀ o ∈ c1.ch.opened, o ∈ c.ch.opened := by
  intro o ho
  rw [hR.opened]
  exact List.mem_append_right _ (List.mem_append_right _ ho)

/-- The rows that the proximity test on the link's group takes in are `LinkDataR.rowsR`. -/
theorem LinkRanR.runRows_eq :
    runRows (linkStR S c.st D.places { D.row0 with target := D.y0 } { D.row1 with target := D.y1 }
        D.rec0 D.rec1 D.rows0 D.rows1 D.rE)
      (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size) = D.rowsR.toArray :=
  linkSt_runRowsR S c.st D.places _ _ D.rec0 D.rec1 D.rows0 D.rows1 D.rE
    (eqRow_target _ _ _ _ _ _ hR.eqRow).2 (recRowsR_kind _ _ _ _ _ hR.rec0)
    (recRowsR_kind _ _ _ _ _ hR.rec1) (columnRows_kind _ _ _ _ _ _ _ _ hR.rows0)
    (columnRows_kind _ _ _ _ _ _ _ _ hR.rows1)

variable {G : Group} {L : GroupLayout} {θ : E} {row : GroupRow}
  (hB : BatRan x.group c1 c2 G L θ row)

include hB

/-- What the link's steps and the batching leave of the codes, the book, the counts, the opened
columns and the named tests. -/
theorem LinkRanR.bat_keeps :
    c2.st.codes = c.st.codes ∧ c2.book = bookSent c (linkMessage S 1) D.lay ∧
      c2.ch.roots = c.ch.roots + D.lay.shapes.size ∧ c2.ch.firstTree = c.ch.firstTree ∧
      c2.ch.dry = false ∧ c2.failed = c.failed ∧ ∀ o ∈ c2.ch.opened, o ∈ c.ch.opened :=
  ⟨by rw [hB.st, begun_codes, hR.codes], hB.book.trans hR.book, hB.roots.trans hR.roots,
    hB.firstTree.trans hR.firstTree, hB.dry, hB.failed.trans hR.failed,
    fun o ho => hR.opened_sub o (hB.opened ▸ ho)⟩

/-- The group and the layout that the batching after the link's steps finds, and what it
combines. -/
theorem LinkRanR.bat_input :
    G = linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size ∧ L = linkLay S c.st ∧
      Bat.combine (begun (linkStR S c.st D.places { D.row0 with target := D.y0 }
          { D.row1 with target := D.y1 } D.rec0 D.rec1 D.rows0 D.rows1 D.rE) c.st.groups.size
          (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)) c.st.groups.size
        ⟨linkLay S c.st, runRows (linkStR S c.st D.places { D.row0 with target := D.y0 }
          { D.row1 with target := D.y1 } D.rec0 D.rec1 D.rows0 D.rows1 D.rE)
          (linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size)⟩ θ = some row := by
  have hG : G = linkGrpR S D.rec0 D.rec1 D.rows0 D.rows1 D.rE c.st.oracles.size := by
    have h := hB.group
    rw [hR.st, hR.group, linkSt_groupR] at h
    exact (Option.some.inj h).symm
  have hL : L = linkLay S c.st := by
    have h := hB.layout
    rw [hR.st, hR.group, linkStR, linkSt_layout _ _ _ _ _ _ _ _ hR.rows_pos] at h
    exact (Option.some.inj h).symm
  have h := hB.row
  rw [hR.st, hR.group, hG, hL] at h
  exact ⟨hG, hL, h⟩

/-- The row that the batching returns is a plain form on the group's main table. -/
theorem LinkRanR.bat_plain : PlainForm row.c := by
  refine combine_plain _ _ _ _ _ (fun r hr => hR.plain r ?_) (hR.bat_input hB).2.2
  have hr' : r ∈ (runRows _ _).toList := hr
  rw [hR.runRows_eq] at hr'
  exact hr'

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

/-- The target of the row that the batching returns: the sum of the rows' targets under the
powers of the drawn element. -/
theorem LinkRanR.bat_target :
    ρ.val row.target =
      ∑ b ∈ Finset.range D.rowsR.length, ρ.val θ ^ b * ρ.val (D.rowsR.getD b default).target :=
  linkBat_target_sumR ρ S c.st D.places _ _ (D.rec0 ++ (D.rec1 ++ D.rows0)) D.rows1 D.rE D.rowsR
    hR.runRows_eq hR.fitsSt θ row (hR.bat_input hB).2.2

/-- The mask table of the row that the batching returns is 0. -/
theorem LinkRanR.bat_mask (J : Nat)
    (hJ : J < 2 ^ ((linkLay S c.st).h + (linkLay S c.st).logEllZk)) :
    ρ.val (row.d.getD J zeroE) = 0 :=
  linkBat_maskR ρ S c.st D.places _ _ (D.rec0 ++ (D.rec1 ++ D.rows0)) D.rows1 D.rE D.rowsR
    hR.runRows_eq hR.fitsSt θ row (hR.bat_input hB).2.2 hR.mainOnly J hJ

/-- A coefficient of the row that the batching returns: at row r of the block of member b, at
the place p, the sum of the rows' coefficients on entry (r, p) of that member's own main table,
under the powers of the drawn element. -/
theorem LinkRanR.bat_main (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    ρ.val (row.c.entry
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)) =
      ∑ i ∈ Finset.range D.rowsR.length, ρ.val θ ^ i * ρ.val ((D.rowsR.getD i default).coefficient
        (if b then c.st.oracles.size + 1 else c.st.oracles.size) .main
        (r + 2 ^ ceilLog2 S.rows * p)) :=
  linkBat_main_sumR ρ S c.st D.places _ _ (D.rec0 ++ (D.rec1 ++ D.rows0)) D.rows1 D.rE D.rowsR
    hR.runRows_eq hR.fitsSt θ row (hR.bat_input hB).2.2 b r p hr

end

end OnBytes.Slice
