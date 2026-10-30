-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkHead.lean: the link's steps and the batching after them, as one run.

OnBytes/Slice/BlkLinkRan.lean writes down what a run of the link's steps is to do (`LinkRan`), and
OnBytes/Slice/BlkBat.lean what a run of the batching has done (`BatRan`). This file puts the two
together. From the first it shows that all rows that are batched meet the conditions of the laws on
batching (`LinkRan.fits`). From both it gives the target and the main-table entries of the row that
the batching returns, in any commutative ring under a reading of the program's field elements,
and what the two runs leave of the codes, the book, the counts and the opened columns.

Main definition: `LinkData.rows`, the rows that are batched, in their order.
Main theorems.
 `LinkRan.fits`   on all rows that are batched.
 `LinkRan.bat_input`    the group, the layout and the combination that the batching finds.
 `LinkRan.bat_keeps`    the codes, the book, the counts and the opened columns after the two runs.
 `LinkRan.bat_target`, `LinkRan.bat_main`   the returned row's target and main-table entries.
Not claimed. What the rows' coefficients are (OnBytes/Slice/BlkLink.lean). Nothing on soundness.
That the batched rows are plain or free of mask tables; the returned row's mask-table entries.
-/
import OnBytes.Slice.BlkBat
import OnBytes.Slice.BlkLink
import OnBytes.Slice.BlkLinkBat
import OnBytes.Slice.BlkPlain

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape FoldeqShape)

/-- Each row of a table's draws is the row of a position and a value. -/
theorem columnRows_each (S : FoldeqShape) (eqGamma : Array E) (pos : Positions) (first : Nat)
    (u : FoldedRow) (list : Array Nat) (columns : Array (Array F)) (rows : List Row)
    (h : columnRows S eqGamma pos first u list columns = some rows) :
    ∀ r ∈ rows, ∃ x y, foldeqColumnRow S x y u = some r := by
  obtain ⟨hl, hk⟩ := colRows_getD S eqGamma u list columns _ rows h
  intro r hr
  obtain ⟨k, hk1, rfl⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨i, col, _, _, h3⟩ := hk k (hl ▸ hk1)
  have e : rows.getD k default = rows[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]
    rfl
  rw [e] at h3
  exact ⟨_, _, h3⟩

/-- The rows of a table's draws are generator rows. -/
theorem columnRows_kind (S : FoldeqShape) (eqGamma : Array E) (pos : Positions) (first : Nat)
    (u : FoldedRow) (list : Array Nat) (columns : Array (Array F)) (rows : List Row)
    (h : columnRows S eqGamma pos first u list columns = some rows) :
    ∀ r ∈ rows, r.kind = .generator := fun r hr => by
  obtain ⟨x, y, h3⟩ := columnRows_each S eqGamma pos first u list columns rows h r hr
  exact (colRow_target _ _ _ _ _ h3).2

/-- A row whose terms have no written-out factor, and that has no whole coefficient vector, is
plain. -/
theorem plainRow_of_terms (r : Row)
    (h : (∀ t ∈ r.terms.toList, t.v.denseVars = []) ∧ r.forms = #[]) : PlainRow r :=
  ⟨h.1, fun f hf => by rw [h.2] at hf; exact absurd hf List.not_mem_nil⟩

/-- The beginning of a test changes no code. -/
theorem begun_codes (S : Statement) (g : Nat) (G : Group) : (begun S g G).codes = S.codes :=
  closeLedgers_codes _ _

section
variable {S : LinkShape} {first further : TableKey} {c c1 c2 : Ctx} {x : LinkRun} {D : LinkData}
  (hR : LinkRan S first further c c1 x D)

/-- The rows that are batched after the link's steps, in their order. -/
def LinkData.rows (D : LinkData) : List Row :=
  D.rE :: { D.row0 with target := D.y0 } :: { D.row1 with target := D.y1 } :: (D.rows0 ++ D.rows1)

include hR

/-- A folded row's oracle message has at least one row. -/
theorem LinkRan.rows_pos : 0 < S.rows := by
  have h := hR.ok
  unfold linkOk Params.LinkShape.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

/-- The point of the seed has as many coordinates as the cube of a folded row's oracle message. -/
theorem LinkRan.seed_length :
    ((D.r2.drawn.elems.map E.ofTriple).take (Send.cube c.st.codes (rowShape S)).bits).length =
      (Send.cube c.st.codes (rowShape S)).bits := by
  have h := congrArg List.length hR.factor
  rw [List.length_drop, List.length_singleton] at h
  rw [List.length_take]
  omega

/-- All rows that are batched meet the conditions of the laws on batching. -/
theorem LinkRan.fits : ∀ r ∈ D.rows, RowFits c1.st r := by
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
    · rw [hR.st, (linkSt_tables S c.st _ _ _ _ _ _ b).2.1]
      show ceilLog2 S.rows ≤ (Send.cube c.st.codes (rowShape S)).mainBits
      have hm : (Send.cube c.st.codes (rowShape S)).hasMain = true := hp
      rw [cube_mainBits_eq, if_pos hm, cube_mainRowBits_eq, if_pos hm]
      exact Nat.le_add_right _ _
    · cases hp
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact rowFits_of_checked (hR.checked _ List.mem_cons_self)
  · rcases List.mem_cons.1 hr with rfl | hr
    · exact rowFits_target _ _ (hsmp false _ hR.form0) _
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact rowFits_target _ _ (hsmp true _ hR.form1) _
      · exact rowFits_of_checked (hR.checked _ (List.mem_cons_of_mem _ hr))

/-- The link's steps change no code. -/
theorem LinkRan.codes : c1.st.codes = c.st.codes := by
  rw [hR.st]
  exact linkSt_codes _ _ _ _ _ _ _ _

/-- The opened columns that the link's steps leave were among those that they found. -/
theorem LinkRan.opened_sub : ∀ o ∈ c1.ch.opened, o ∈ c.ch.opened := by
  intro o ho
  rw [hR.opened]
  exact List.mem_append_right _ (List.mem_append_right _ ho)

variable {G : Group} {L : GroupLayout} {θ : E} {row : GroupRow}
  (hB : BatRan x.group c1 c2 G L θ row)

include hB

/-- What the link's steps and the batching leave of the codes, the book, the counts, the opened
columns and the named tests. -/
theorem LinkRan.bat_keeps :
    c2.st.codes = c.st.codes ∧ c2.book = bookSent c (linkMessage S 1) D.lay ∧
      c2.ch.roots = c.ch.roots + D.lay.shapes.size ∧ c2.ch.firstTree = c.ch.firstTree ∧
      c2.ch.dry = false ∧ c2.failed = c.failed ∧ ∀ o ∈ c2.ch.opened, o ∈ c.ch.opened :=
  ⟨by rw [hB.st, begun_codes, hR.codes], hB.book.trans hR.book, hB.roots.trans hR.roots,
    hB.firstTree.trans hR.firstTree, hB.dry, hB.failed.trans hR.failed,
    fun o ho => hR.opened_sub o (hB.opened ▸ ho)⟩

/-- The group and the layout that the batching after the link's steps finds, and what it
combines. -/
theorem LinkRan.bat_input :
    G = linkGrp S D.rows0 D.rows1 D.rE c.st.oracles.size ∧ L = linkLay S c.st ∧
      Bat.combine (begun (linkSt S c.st D.places { D.row0 with target := D.y0 }
          { D.row1 with target := D.y1 } D.rows0 D.rows1 D.rE) c.st.groups.size
          (linkGrp S D.rows0 D.rows1 D.rE c.st.oracles.size)) c.st.groups.size
        ⟨linkLay S c.st, runRows (linkSt S c.st D.places { D.row0 with target := D.y0 }
          { D.row1 with target := D.y1 } D.rows0 D.rows1 D.rE)
          (linkGrp S D.rows0 D.rows1 D.rE c.st.oracles.size)⟩ θ = some row := by
  have hG : G = linkGrp S D.rows0 D.rows1 D.rE c.st.oracles.size := by
    have h := hB.group
    rw [hR.st, hR.group, linkSt_group] at h
    exact (Option.some.inj h).symm
  have hL : L = linkLay S c.st := by
    have h := hB.layout
    rw [hR.st, hR.group, linkSt_layout _ _ _ _ _ _ _ _ hR.rows_pos] at h
    exact (Option.some.inj h).symm
  have h := hB.row
  rw [hR.st, hR.group, hG, hL] at h
  exact ⟨hG, hL, h⟩

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

/-- The target of the row that the batching returns: the sum of the rows' targets under the
powers of the drawn element. -/
theorem LinkRan.bat_target :
    ρ.val row.target =
      ∑ b ∈ Finset.range D.rows.length, ρ.val θ ^ b * ρ.val (D.rows.getD b default).target :=
  linkBat_target_sum ρ S c.st D.places _ _ D.rows0 D.rows1 D.rE
    (eqRow_target _ _ _ _ _ _ hR.eqRow).2 (columnRows_kind _ _ _ _ _ _ _ _ hR.rows0)
    (columnRows_kind _ _ _ _ _ _ _ _ hR.rows1) (fun r hr => hR.st ▸ hR.fits r hr) θ row
    (hR.bat_input hB).2.2

/-- A coefficient of the row that the batching returns: at row r of the block of member b, at
the place p, the sum of the rows' coefficients on entry (r, p) of that member's own main table,
under the powers of the drawn element. -/
theorem LinkRan.bat_main (b : Bool) (r p : Nat) (hr : r < 2 ^ ceilLog2 S.rows) :
    ρ.val (row.c.entry
      ((if b then 2 ^ ceilLog2 S.rows else 0) + r + 2 ^ (ceilLog2 S.rows + 1) * p)) =
      ∑ i ∈ Finset.range D.rows.length, ρ.val θ ^ i * ρ.val ((D.rows.getD i default).coefficient
        (if b then c.st.oracles.size + 1 else c.st.oracles.size) .main
        (r + 2 ^ ceilLog2 S.rows * p)) :=
  linkBat_main_sum ρ S c.st D.places _ _ D.rows0 D.rows1 D.rE
    (eqRow_target _ _ _ _ _ _ hR.eqRow).2 (columnRows_kind _ _ _ _ _ _ _ _ hR.rows0)
    (columnRows_kind _ _ _ _ _ _ _ _ hR.rows1) (fun r hr => hR.st ▸ hR.fits r hr) θ row
    (hR.bat_input hB).2.2 b r p hr

end

end OnBytes.Slice

#print axioms OnBytes.Slice.columnRows_each
#print axioms OnBytes.Slice.columnRows_kind
#print axioms OnBytes.Slice.plainRow_of_terms
#print axioms OnBytes.Slice.begun_codes
#print axioms OnBytes.Slice.LinkRan.rows_pos
#print axioms OnBytes.Slice.LinkRan.seed_length
#print axioms OnBytes.Slice.LinkRan.fits
#print axioms OnBytes.Slice.LinkRan.codes
#print axioms OnBytes.Slice.LinkRan.opened_sub
#print axioms OnBytes.Slice.LinkRan.bat_keeps
#print axioms OnBytes.Slice.LinkRan.bat_input
#print axioms OnBytes.Slice.LinkRan.bat_target
#print axioms OnBytes.Slice.LinkRan.bat_main
