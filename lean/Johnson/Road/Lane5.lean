-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5.lean

What it means that the 25 links of a proof file's first chain are in order, and that then all 25
segments' conditions hold at ONE family of integer matrices.

At the full size a proof file's first chain has 25 links: two for each of the 12 groups of layers,
and the head's. They stand one for one where the library's model has its 25 segments: link 2 g is
the first segment of group g of layers, link 2 g + 1 its attention segment, link 24 the head. (That
the chain has these links in this order is read in the programs' text; no theorem here says it.)

The premise speaks of integer matrices, one integer matrix of weights and the request. It names no
hidden value of a sub-proof, no challenge and no claim. Whether a proof file that a verifier accepts
has such matrices is not looked at here: that is the soundness of the links.

Each link k has matrices "A k" of its own: what the arrays of its own sub-proof hold, that is its
own cells and its copies of cells that an earlier link owns. The field "seam" says: at every place
that segment k may read ("Cm.Seg.reads"), link k holds what the owner's link holds there. Nothing is
asked of an array that merely passes through a link. Bound and seam are asked at places of cells
alone: nothing is asked where no cell stands.

The file is written for any shape h of the head and any family "seg" of 25 segments that is well
formed and reads what the library's layout says ("SegLaws"). It has two uses: the plain head and
the head with the cost ledger (Lane5Ledger.lean).

Main definitions and theorems:
* "LinkOK h seg Wz x k A": link k is in order: its own cells are below 2^18, every identity of
  segment k is 0, every key of segment k is an entry of its table. The last two fields are, to the
  letter, the two halves of the library's "Cb.SegSpec.Holds".
* "Premise h seg Wz x A": all 25 links are in order, and the seam holds.
* "one A": the cells of each segment as its own link holds them.
* "holds_one", "small_one": under the premise all segments' conditions hold at "one A"
  ("Cb.Req.holds_congr": a segment's conditions read its places alone), and its cells are small.
* "seam_of_neighbours": the seam follows if every cell in a row that the library keeps behind
  segment k ("Cm.Seg.kept k") is the same in link k + 1 as in link k ("Cm.lay_keeps": a borrowed
  row is kept behind every segment in between). This asks a reading of the kept rows in EVERY link
  between owner and reader; the field "seam" does not.

Not claimed: that any program or protocol shows the premise; whose matrices "A k" are; anything at
other sizes than the reference.

-/
import Cm.TargetSegAll
import Cm.SegLayoutProofs
import Cb.Req.ReqCellsProofs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-! ## 1. The premise -/

/-- Integer matrices: segment, row, column. The library's own type for the cells of the model. -/
abbrev Mx : Type := ℕ → ℕ → ℕ → ℤ

/-- A family of segments over the protocol's fields. -/
abbrev Segs : Type := ℕ → Cb.SegSpec (Instance ppref) Cb.Gl.F Cb.Gl.E

/-- **Link k is in order** at the matrices A, the integer matrix Wz of weights and the request x. -/
structure LinkOK (h : Cm.Seg.Hd) (seg : Segs) (Wz : Mat) (x : Instance ppref) (k : ℕ) (A : Mx) :
    Prop where
  small : ∀ n : Cm.Seg.Name, n.Valid h → n.place.1 = k → |Cm.Seg.at' A n.place| < 2 ^ 18
  idn : ∀ f ∈ (seg k).idn, ∀ b < 2 ^ f.v,
    f.val Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A) b = 0
  key : ∀ q ∈ (seg k).keys, ∀ b < 2 ^ q.1.v, ∃ u ∈ q.2.set,
    q.1.val Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A) b =
      algebraMap Cb.Gl.F Cb.Gl.E u

/-- **The premise**: every link is in order at its own matrices, and holds at every place that its
segment may read what the owner's link holds there. -/
structure Premise (h : Cm.Seg.Hd) (seg : Segs) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) :
    Prop where
  link : ∀ k < Cm.Seg.nSeg, LinkOK h seg Wz x k (A k)
  seam : ∀ k < Cm.Seg.nSeg, ∀ q ∈ Cm.Seg.reads h k, Cm.Seg.at' (A k) q = Cm.Seg.at' (A q.1) q

/-- What is asked of the shape of the head and of the family of segments. -/
structure SegLaws (h : Cm.Seg.Hd) (seg : Segs) : Prop where
  ok : h.OK
  wf : ∀ k < Cm.Seg.nSeg, (seg k).WF Cm.Seg.TS.fmtRef
  places : ∀ k < Cm.Seg.nSeg, ∀ q ∈ (seg k).places, q ∈ Cm.Seg.reads h k

/-- One family of matrices: the cells of each segment as its own link holds them. -/
def one (A : ℕ → Mx) : Mx := fun k r c => A k k r c

variable {h : Cm.Seg.Hd} {seg : Segs} {Wz : Mat} {x : Instance ppref}

/-- The two halves are the conditions of the segment. -/
theorem LinkOK.holds {k : ℕ} {A : Mx} (H : LinkOK h seg Wz x k A) :
    (seg k).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A) :=
  ⟨H.idn, H.key⟩

/-- A link is in order if its own cells are small and the conditions of its segment hold. -/
theorem linkOK_of_holds {k : ℕ} {A : Mx}
    (hb : ∀ n : Cm.Seg.Name, n.Valid h → n.place.1 = k → |Cm.Seg.at' A n.place| < 2 ^ 18)
    (H : (seg k).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A)) :
    LinkOK h seg Wz x k A :=
  ⟨hb, H.1, H.2⟩

/-! ## 2. One family of matrices -/

/-- **All segments' conditions hold at one family of matrices.** -/
theorem holds_one {A : ℕ → Mx} (L : SegLaws h seg) (P : Premise h seg Wz x A) {k : ℕ}
    (hk : k < Cm.Seg.nSeg) :
    (seg k).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM (one A)) :=
  Cb.Req.holds_congr (L.wf k hk)
    (fun q hq => congrArg (fun z : ℤ => (z : Cb.Gl.E)) (P.seam k hk q (L.places k hk q hq)))
    (P.link k hk).holds

/-- All cells of that family are below 2^18. -/
theorem small_one {A : ℕ → Mx} (L : SegLaws h seg) (P : Premise h seg Wz x A) (n : Cm.Seg.Name)
    (hn : n.Valid h) : |Cm.Seg.at' (one A) n.place| < 2 ^ 18 :=
  (P.link n.place.1 (Cm.lay_inShape h L.ok n hn).1).small n hn rfl

/-! ## 3. The seam from neighbours -/

/-- A place that a segment may read is the place of a cell. -/
theorem reads_name {k : ℕ} {q : Cb.Place} (hq : q ∈ Cm.Seg.reads h k) :
    ∃ n : Cm.Seg.Name, n.Valid h ∧ n.place = q := by
  rcases hq with ⟨g, c, _, hg, hc, e⟩ | ⟨g, c, _, hg, hc, e⟩ |
    ⟨_, ⟨n, hn, _, e⟩ | ⟨φ, i, hφ, hi, e⟩⟩
  · exact ⟨_, (Cm.lay_own_valid h).1 g hg c hc, e.symm⟩
  · exact ⟨_, (Cm.lay_own_valid h).2.1 g hg c hc, e.symm⟩
  · exact ⟨n, hn, e.symm⟩
  · exact ⟨_, (Cm.lay_own_valid h).2.2 φ hφ i hi, e.symm⟩

/-- **If kept cells are the same from each link to the next, the seam holds.** -/
theorem seam_of_neighbours (hh : h.OK) {A : ℕ → Mx}
    (hseam : ∀ k, k + 1 < Cm.Seg.nSeg → ∀ n : Cm.Seg.Name, n.Valid h →
      (n.place.1, n.place.2.1) ∈ Cm.Seg.kept k →
      Cm.Seg.at' (A (k + 1)) n.place = Cm.Seg.at' (A k) n.place)
    {k : ℕ} (hk : k < Cm.Seg.nSeg) {q : Cb.Place} (hq : q ∈ Cm.Seg.reads h k) :
    Cm.Seg.at' (A k) q = Cm.Seg.at' (A q.1) q := by
  obtain ⟨n, hn, rfl⟩ := reads_name hq
  have hle : n.place.1 ≤ k := (Cm.lay_reads h hh k hk n.place hq).1
  have step : ∀ d, n.place.1 + d ≤ k →
      Cm.Seg.at' (A (n.place.1 + d)) n.place = Cm.Seg.at' (A n.place.1) n.place := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have h1 := hseam (n.place.1 + d) (by omega) n hn
        (Cm.lay_keeps h hh k hk n.place hq (n.place.1 + d) (by omega) (by omega))
      exact h1.trans (ih (by omega))
  have h2 := step (k - n.place.1) (by omega)
  rwa [Nat.add_sub_cancel' hle] at h2

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.holds_one
#print axioms OnBytes.Road.L5.small_one
#print axioms OnBytes.Road.L5.reads_name
#print axioms OnBytes.Road.L5.seam_of_neighbours
