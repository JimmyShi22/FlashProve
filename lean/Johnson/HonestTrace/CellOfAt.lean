-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CellOfAt.lean

The reader by labels "cellOf" (Johnson/HonestTrace/Full.lean) at the places of the library's rules:
what it returns at a label, and that at the place of a valid name of any of the three sorts of
segment it returns the image of the honest cell.

"cellOf X T k s r c" reads a trace T by the sub-proof's number k, a string s for the matrix, a row
of cells and a column. It has no rule of places in it: row and column are the caller's. Where the
cell of a name stands (number in the list, row, column) is a rule of the library for each sort of
segment: "placeOf" (Johnson/Road/FormsKeysAddr.lean) for a feed-forward segment, "addrA"
(Johnson/Road/Lane5AttDef.lean) for an attention segment, "placeH" (Johnson/HonestTrace/Full.lean)
for the head. The bundle "MeetsAll" says that the library's readers, which go by these rules, find
the honest cells. This file joins the two, with no premise on public files: the numbers of parts are
a premise ("PartsFit", Johnson/HonestTrace/FromCells.lean).

Main theorems:
* "cellOf_label": under "PartsFit X", for every trace T, every segment σ of a proof with 12 groups
  and every name μ that has the number a in σ's list at the numbers of parts 3, 1, 1, 4: "cellOf X
  T" at σ's number and μ's label is the image in the field F of the entry of T at σ's number and a.
* "cellOf_placeOf": under "PartsFit X" and "MeetsAll X i x T", for g < 12 and a valid name q of a
  feed-forward segment: if μ is the name with the number that "placeOf" gives q, "cellOf X T" at 2
  g, μ's label and the row and column that "placeOf" gives q is the image in F of the honest cell
  "(honAt X i x).vFF g q".
* "cellOf_placeH": the same for the head: at sub-proof 24, for a position below 1,024 and a feature
  that holds a cell of hf, hd, hr or of the borrowed stream, by "placeH" and "(honAt X i x).vHead".
* "cellOf_addrA": under "PartsFit X" and "MeetsAll X i x T", for g < 12 and a valid name q of an
  attention segment: if μ is the name with the number that "addrA" gives q, "cellOf X T" at 2 g + 1,
  μ's label and the row and column that "addrA" gives q is the image in F of the honest cell
  "(honAt X i x).vAtt g q".
* "cellOf_ah", "cellOf_ao", "cellOf_qa": the same with the label spelt out, for the names whose
  cells lie in ah (mx, den, ib), in ao (qh, qh') and in the borrowed qa (qry, out, key, val).
* "cellOf_as": the same for the cells of an entry of a region, at the label "as0", if "addrA" gives
  the name the number 0. "addrA_no": which number "addrA" gives a name of each other kind.

Limits. All is at the reference model's sizes and at the numbers of parts 3, 1, 1, 4. "PartsFit" and
"MeetsAll" are premises here; for public files in the goals' scope they are paid in
Johnson/Goal/HonestTrace/FullInScope.lean ("parts_in_scope", "meetsAll_in_scope": the second at a
request that is served). That "addrA" gives every valid name of an entry the number 0 is a premise
of "cellOf_as": it is not shown in this file. A valid name of an entry can be an empty place of
region M or a pair above the diagonal in region D: the honest cell there is what the library's term
is, not 0.

Not claimed: that a prover's committed cells are these; anything on a proof.

-/
import Johnson.HonestTrace.FromCells

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road
open OnBytes.Road.L5 (addrA cellsA zAt)
open OnBytes.Model.Verify (borderOf)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **The reader by labels finds the matrix with the name's number.** Under "PartsFit X", for every
trace T, every segment σ of a proof with 12 groups and every name μ that has the number a in σ's
list at the numbers of parts 3, 1, 1, 4: "cellOf X T" at σ's number and μ's label is the image in
the field of the entry of T at σ's number and a. -/
theorem cellOf_label (N : PartsFit X) (T : Tr) {σ : Seg} (hσ : σ.Below 12) {μ : MatName} {a : ℕ}
    (ha : MatName.no? 3 1 1 4 σ μ = some a) (r c : ℕ) :
    cellOf X T (σ.no 12) μ.label r c = ((T (σ.no 12) a r c : ℤ) : Cb.Gl.F) := by
  obtain ⟨-, e2, e3⟩ := parts_at N (Seg.ofNo_no hσ)
  have hf : MatName.ofLabel? (X.y.parts.getD 0 0) (X.y.parts.getD 1 0)
      (Hd.shapeA X (σ.no 12 / 2)).cf.NAs X.hS.NHf σ μ.label = some μ := by
    rw [e3]
    exact MatName.ofLabel?_label_ref σ μ (MatName.mem_all_of_no? ha)
  have hn : noAt X σ μ = some a := by
    unfold noAt
    rw [e2, ha]
  unfold cellOf
  rw [Seg.ofNo_no hσ]
  simp only
  rw [hf]
  simp only
  unfold byName
  rw [if_pos (Seg.ofNo_no hσ), hn]

/-- **At the place of a valid name of a feed-forward segment the reader by labels returns the honest
cell.** Under "PartsFit X" and "MeetsAll X i x T", for g < 12 and q valid at the reference sizes: if
μ has, in the list of the feed-forward segment of group g, the number that "placeOf" gives q, then
"cellOf X T" at 2 g, μ's label and the row and column that "placeOf" gives q is the image in the
field of "(honAt X i x).vFF g q". The name x0 of a later group is valid: its cell stands in the
borrowed xbI. -/
theorem cellOf_placeOf (N : PartsFit X) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12)
    {q : FFSeg.Cell} (hq : q.Valid DF) {μ : MatName}
    (hμ : MatName.no? 3 1 1 4 (.ff g) μ = some (placeOf X.y DF q).1) :
    cellOf X T (2 * g) μ.label (placeOf X.y DF q).2.1 (placeOf X.y DF q).2.2 =
      (((honAt X i x).vFF g q : ℤ) : Cb.Gl.F) := by
  have e := cellOf_label N T (σ := .ff g) hg hμ (placeOf X.y DF q).2.1 (placeOf X.y DF q).2.2
  have e' : cellOf X T (2 * g) μ.label (placeOf X.y DF q).2.1 (placeOf X.y DF q).2.2 =
      ((cellsOf DF (cellsAt X.y (T (2 * g))) q : ℤ) : Cb.Gl.F) := e
  rw [e', M.readG g hg q hq]

/-- **At the place of a feature of the head the reader by labels returns the honest cell.** Under
"PartsFit X" and "MeetsAll X i x T", for a position t below 1,024, for each of the matrices hf, hd,
hr and the borrowed stream x, and a feature φ that holds a cell of it: if μ has, in the head's list,
the number that "placeH" gives (φ, t), then "cellOf X T" at 24, μ's label and the row and column
that "placeH" gives is the image in the field of that matrix's entry (φ, t) of
"(honAt X i x).vHead". -/
theorem cellOf_placeH (N : PartsFit X) (M : MeetsAll X i x T) {t : ℕ} (ht : t < Head.nT) :
    (∀ φ < Head.nFeat .hf, ∀ μ : MatName,
      MatName.no? 3 1 1 4 .head μ = some (placeH X .hf φ t).1 →
      cellOf X T 24 μ.label (placeH X .hf φ t).2.1 (placeH X .hf φ t).2.2 =
        (((honAt X i x).vHead.hf φ t : ℤ) : Cb.Gl.F)) ∧
    (∀ φ < Head.nFeat .hd, ∀ μ : MatName,
      MatName.no? 3 1 1 4 .head μ = some (placeH X .hd φ t).1 →
      cellOf X T 24 μ.label (placeH X .hd φ t).2.1 (placeH X .hd φ t).2.2 =
        (((honAt X i x).vHead.hd φ t : ℤ) : Cb.Gl.F)) ∧
    (∀ φ < Head.nFeat .hr, ∀ μ : MatName,
      MatName.no? 3 1 1 4 .head μ = some (placeH X .hr φ t).1 →
      cellOf X T 24 μ.label (placeH X .hr φ t).2.1 (placeH X .hr φ t).2.2 =
        (((honAt X i x).vHead.hr φ t : ℤ) : Cb.Gl.F)) ∧
    ∀ φ < Head.nFeat .x, ∀ μ : MatName,
      MatName.no? 3 1 1 4 .head μ = some (placeH X .x φ t).1 →
      cellOf X T 24 μ.label (placeH X .x φ t).2.1 (placeH X .x φ t).2.2 =
        (((honAt X i x).vHead.x φ t : ℤ) : Cb.Gl.F) := by
  obtain ⟨r1, r2, r3, r4⟩ := M.readH t ht
  refine ⟨fun φ hφ μ hμ => ?_, fun φ hφ μ hμ => ?_, fun φ hφ μ hμ => ?_, fun φ hφ μ hμ => ?_⟩
  · rw [← r1 φ hφ, (cellsH_placeH X (T 24) φ t).1]
    exact cellOf_label N T (σ := .head) trivial hμ _ _
  · rw [← r2 φ hφ, (cellsH_placeH X (T 24) φ t).2.1]
    exact cellOf_label N T (σ := .head) trivial hμ _ _
  · rw [← r3 φ hφ, (cellsH_placeH X (T 24) φ t).2.2.1]
    exact cellOf_label N T (σ := .head) trivial hμ _ _
  · rw [← r4 φ hφ, (cellsH_placeH X (T 24) φ t).2.2.2]
    exact cellOf_label N T (σ := .head) trivial hμ _ _

/-- **At the place of a valid name of an attention segment the reader by labels returns the honest
cell.** Under "PartsFit X" and "MeetsAll X i x T", for g < 12 and q valid at the reference sizes: if
μ has, in the list of the attention segment of group g, the number that "addrA" gives q, then
"cellOf X T" at 2 g + 1, μ's label and the row and column that "addrA" gives q is the image in the
field of "(honAt X i x).vAtt g q". -/
theorem cellOf_addrA (N : PartsFit X) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12)
    {q : AttSeg.Raw} (hq : q.Valid DA) {μ : MatName}
    (hμ : MatName.no? 3 1 1 4 (.att g) μ = some (addrA (Hd.shapeA X g) q).1) :
    cellOf X T (2 * g + 1) μ.label (addrA (Hd.shapeA X g) q).2.1 (addrA (Hd.shapeA X g) q).2.2 =
      (((honAt X i x).vAtt g q : ℤ) : Cb.Gl.F) := by
  have e := cellOf_label N T (σ := .att g) hg hμ (addrA (Hd.shapeA X g) q).2.1
    (addrA (Hd.shapeA X g) q).2.2
  have e' : cellOf X T (2 * g + 1) μ.label (addrA (Hd.shapeA X g) q).2.1
      (addrA (Hd.shapeA X g) q).2.2 =
      ((cellsA (Hd.shapeA X g) (T (2 * g + 1)) q : ℤ) : Cb.Gl.F) := e
  rw [e', M.readA g hg q hq]

/-- "cellOf_addrA" at a name whose cell "addrA" puts in the matrix number NAs: the label is "ah".
These are the names mx, den and ib. -/
theorem cellOf_ah (N : PartsFit X) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) {q : AttSeg.Raw}
    (hq : q.Valid DA) (hn : (addrA (Hd.shapeA X g) q).1 = (Hd.shapeA X g).cf.NAs) :
    cellOf X T (2 * g + 1) "ah" (addrA (Hd.shapeA X g) q).2.1 (addrA (Hd.shapeA X g) q).2.2 =
      (((honAt X i x).vAtt g q : ℤ) : Cb.Gl.F) :=
  cellOf_addrA N M hg hq (μ := .ah) (by rw [hn, N.as g hg]; rfl)

/-- "cellOf_addrA" at a name whose cell "addrA" puts in the matrix number NAs + 1: the label is
"ao". These are the names qh and qh'. -/
theorem cellOf_ao (N : PartsFit X) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) {q : AttSeg.Raw}
    (hq : q.Valid DA) (hn : (addrA (Hd.shapeA X g) q).1 = (Hd.shapeA X g).cf.NAs + 1) :
    cellOf X T (2 * g + 1) "ao" (addrA (Hd.shapeA X g) q).2.1 (addrA (Hd.shapeA X g) q).2.2 =
      (((honAt X i x).vAtt g q : ℤ) : Cb.Gl.F) :=
  cellOf_addrA N M hg hq (μ := .ao) (by rw [hn, N.as g hg]; rfl)

/-- "cellOf_addrA" at a name whose cell "addrA" puts in the matrix number NAs + 3: the label is
"qa". These are the borrowed names qry, out, key and val. -/
theorem cellOf_qa (N : PartsFit X) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) {q : AttSeg.Raw}
    (hq : q.Valid DA) (hn : (addrA (Hd.shapeA X g) q).1 = (Hd.shapeA X g).cf.NAs + 3) :
    cellOf X T (2 * g + 1) "qa" (addrA (Hd.shapeA X g) q).2.1 (addrA (Hd.shapeA X g) q).2.2 =
      (((honAt X i x).vAtt g q : ℤ) : Cb.Gl.F) :=
  cellOf_addrA N M hg hq (μ := .qa) (by rw [hn, N.as g hg]; rfl)

/-- "cellOf_addrA" at a name whose cell "addrA" puts in the matrix number 0: the label is "as0". -/
theorem cellOf_as (N : PartsFit X) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) {q : AttSeg.Raw}
    (hq : q.Valid DA) (hn : (addrA (Hd.shapeA X g) q).1 = 0) :
    cellOf X T (2 * g + 1) "as0" (addrA (Hd.shapeA X g) q).2.1 (addrA (Hd.shapeA X g) q).2.2 =
      (((honAt X i x).vAtt g q : ℤ) : Cb.Gl.F) :=
  cellOf_addrA N M hg hq (μ := .as 0) (by rw [hn]; rfl)

/-- The numbers that "addrA" gives, by the kind of the name; they hold by unfolding. -/
theorem addrA_no (S : Attention.Shape) :
    (∀ k b g i, (addrA S (.mx k b g i)).1 = S.cf.NAs) ∧
    (∀ k b g i, (addrA S (.den k b g i)).1 = S.cf.NAs) ∧
    (∀ k b g i, (addrA S (.ib k b g i)).1 = S.cf.NAs) ∧
    (∀ b g i n, (addrA S (.qh b g i n)).1 = S.cf.NAs + 1) ∧
    (∀ b g i n, (addrA S (.qh' b g i n)).1 = S.cf.NAs + 1) ∧
    (∀ k b g i n, (addrA S (.qry k b g i n)).1 = S.cf.NAs + 3) ∧
    (∀ k b g i n, (addrA S (.out k b g i n)).1 = S.cf.NAs + 3) ∧
    (∀ k lam g j n, (addrA S (.key k lam g j n)).1 = S.cf.NAs + 3) ∧
    (∀ k lam g j n, (addrA S (.val k lam g j n)).1 = S.cf.NAs + 3) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.cellOf_label
#print axioms OnBytes.HonestTrace.cellOf_placeOf
#print axioms OnBytes.HonestTrace.cellOf_placeH
#print axioms OnBytes.HonestTrace.cellOf_addrA
#print axioms OnBytes.HonestTrace.cellOf_ah
#print axioms OnBytes.HonestTrace.cellOf_ao
#print axioms OnBytes.HonestTrace.cellOf_qa
#print axioms OnBytes.HonestTrace.cellOf_as
#print axioms OnBytes.HonestTrace.addrA_no
