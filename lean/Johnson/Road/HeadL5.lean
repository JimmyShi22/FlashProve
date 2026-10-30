-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5.lean: "the head's link is in order", as a statement on the integer matrices of
the verifier's list for the head's sub-proof.

The library's model has 25 segments (Cm/TargetSegModel.lean: segM). Its conditions on segment 24
speak of one family of integer matrices, indexed by (segment, row, column). The verifier in OnBytes/
has, for the head's sub-proof, a list of matrices, indexed by (number in the list, row, column);
one of them, number NHf + 3, is its copy of the stream that the last group of layers hands on. This
file fills the library's family from that list alone (headMx) and shows that two statements are then
one: every entry is small and the conditions of segment 24 hold at headMx; every entry is small and
keys and identities of the library's plain head hold at the cells that the verifier's rule reads in
the list. No world, slot, challenge or claim occurs.

Main definitions: headMx; HeadOrd (the statement on the integer matrices behind the head's
sub-proof, numbered as the verifier's list numbers them).
Main theorems: portNo_slotNo, stackedH_libOf (the dictionary of Johnson/Road/HeadPlace.lean and that
of Johnson/Road/FormsKeysDict.lean are one on the feed-forward segments, inside the library's
shape); link24_of_ord, ord_of_link24, link24_iff; ord_of_rf.

What is not claimed. Nothing derives HeadOrd from a proof file. The sizes are the library's
reference sizes (FullH, Switches, Sized, Sized2). headMx holds the head's copy of the stream in
every slot of every feed-forward segment, not in slot 7 of segment 22 alone; the conditions of
segment 24 read it there alone. That the copy is the lender's matrix is not said: it is a matter
between two links. The program does not import this file.
-/
import Johnson.Road.HeadSeg
import Johnson.Road.FormsKeysDict
import Cm.TargetSegHeadY
import Cm.TargetSegModel

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat)
open Inst.Model.Head (nT nD nV)
open Inst.Model.All (DF)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)

/-! ## One dictionary on the feed-forward segments -/

/-- The two maps from a slot of the library's matrix of a feed-forward segment to a number in the
verifier's list agree on the eight slots. -/
theorem portNo_slotNo (y : Lay) {s : ℕ} (hs : s < 8) : portNo y s = slotNo y s := by
  have h : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- On a feed-forward segment, at a row of the library's shape, the family that is stacked from the
verifier's lists is the family of Johnson/Road/FormsKeysDict.lean. -/
theorem stackedH_libOf (y : Lay) (Mg : ℕ → Mats ℤ) (Ma : ℕ → ℕ → ℕ → ℤ) (Mh : Mats ℤ) {s r : ℕ}
    (h2 : s % 2 = 0) (h24 : s ≠ 24) (hr : r < 2 ^ 19) (c : ℕ) :
    stackedH y Mg Ma Mh s r c = libOf y Mg s r c := by
  have h8 : r / 65536 < 8 := by omega
  have e : portNo y (r / 65536) = slotNo y (r / 65536) := portNo_slotNo y h8
  show (if s = 24 then Mh (r / 65536) (r % 65536) c
      else if s % 2 = 0 then Mg (s / 2) (slotNo y (r / 65536)) (r % 65536) c
      else Ma (s / 2) r c) =
    if s % 2 = 0 then Mg (s / 2) (portNo y (r / 65536)) (r % 65536) c else 0
  rw [if_neg h24, if_pos h2, if_pos h2, e]

/-! ## The head's link -/

/-- The library's family of matrices, filled from the list Mh of the head's sub-proof alone: segment
24 slot by slot, and the head's copy of the stream wherever a feed-forward segment is read. -/
def headMx (h : Model.Head.Shape) (y : Lay) (Mh : Mats ℤ) : ℕ → ℕ → ℕ → ℤ :=
  stackedH y (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0) Mh

/-- The head's link is in order, said of the matrices Mh of the head's list: every entry is below
2^18 in absolute value, at every number, row and column (Johnson/Road/HeadL5B.lean has the bound
inside the matrices' own rows and columns); and at the cells cellsH every key of the plain head is
in its table and every identity of the final normalisation is 0, modulo the protocol's prime. A cell
is named by the library's number of a feature; the verifier's rule gives a feature its part, row and
column. Keys, identities and tables are the library's. Wz: an integer matrix of the weights' digits,
read by the library's layout (Cm.TP.castH); it is a matrix of no sub-proof. -/
def HeadOrd (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (Wz : Mat)
    (x : Instance ppref) (Mh : Mats ℤ) : Prop :=
  (∀ a r c, |Mh a r c| < 2 ^ 18) ∧
  (∀ f a i, a < Cm.Plain.len f → i < nT → Inst.Model.Head.InLut (Cm.Plain.TP.tableOf f)
    (Cm.Plain.TP.key np ((cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
      (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x) f a i)) ∧
  ∀ i < nT, ∀ k < 17, Cm.Plain.idn np ((cellsH h L (borderOf y) Mh).cast Cb.Gl.F) i k = 0

section Link

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- The conditions of segment 24 of the library's model, at any integer matrices A, are the
conditions of the plain head's segment there, for a request with e = 1,024. -/
theorem segM24_iff (s : Cm.Scales) (x : Instance ppref) (he : x.e = 1024) (Wz : Mat)
    (A : ℕ → ℕ → ℕ → ℤ) :
    (Cm.Seg.TS.segM s 24).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A) ↔
      Down.MatHolds s.nf x Wz A := by
  have e : Cm.Seg.TS.segM s 24 = Cm.Seg.TS.segHeadY s.nf := Cm.Seg.TS.seg_head s _
  rw [e, Cm.Seg.TS.headY_holds, Down.matHolds_iff_seg]
  exact ⟨fun a => a.1, fun a => ⟨a, fun hlt => absurd hlt (by rw [he]; decide)⟩⟩

/-- **All entries small and the conditions of segment 24, if and only if HeadOrd.** Left: all
entries of the list are small, and the conditions of segment 24 of the library's model hold at
headMx. Right: HeadOrd. The two sides say the same along a renumbering of places: nothing is
derived. The left side is more than LinkOK of Johnson/Road/Lane5.lean, whose bound speaks of own
cells alone. -/
theorem link24_iff (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    (s : Cm.Scales) (x : Instance ppref) (he : x.e = 1024) (Wz : Mat) (Mh : Mats ℤ) :
    ((∀ a r c, |Mh a r c| < 2 ^ 18) ∧
      (Cm.Seg.TS.segM s 24).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
        (Cm.Seg.TS.cM (headMx h y Mh))) ↔ HeadOrd h L y s.nf Wz x Mh := by
  unfold HeadOrd headMx
  rw [segM24_iff s x he Wz,
    matHolds_iff_cells hF hL hl S Z Z2 _ _ Mh (fun _ _ _ _ => rfl) s.nf x Wz]

/-- From the verifier's matrices to the library's three clauses on link 24: small in the library's
shape, and the conditions of segment 24 (its identities and its keys). -/
theorem link24_of_ord (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {s : Cm.Scales} {x : Instance ppref} (he : x.e = 1024) {Wz : Mat} {Mh : Mats ℤ}
    (O : HeadOrd h L y s.nf Wz x Mh) :
    (∀ r c, Cm.Seg.InShape (24, r, c) → |headMx h y Mh 24 r c| < 2 ^ 18) ∧
      (Cm.Seg.TS.segM s 24).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
        (Cm.Seg.TS.cM (headMx h y Mh)) :=
  ⟨fun _ _ _ => O.1 _ _ _, ((link24_iff hF hL hl S Z Z2 s x he Wz Mh).2 O).2⟩

/-- From small entries and the conditions of segment 24 at headMx back to HeadOrd. -/
theorem ord_of_link24 (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {s : Cm.Scales} {x : Instance ppref} (he : x.e = 1024) {Wz : Mat} {Mh : Mats ℤ}
    (small : ∀ a r c, |Mh a r c| < 2 ^ 18)
    (H : (Cm.Seg.TS.segM s 24).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
      (Cm.Seg.TS.cM (headMx h y Mh))) : HeadOrd h L y s.nf Wz x Mh :=
  (link24_iff hF hL hl S Z Z2 s x he Wz Mh).1 ⟨small, H⟩

/-- From the field relation of the plain head over the challenge field, at the cells that are read
in small integer matrices, to HeadOrd. The field relation is what the theorems on the verifier's
claims conclude (head_link_rf_of_port in Johnson/Road/HeadLinkPort.lean). Hz:
the output matrix; it is what the library's layout reads in the digits Wz. -/
theorem ord_of_rf (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {np : NormPar} {x : Instance ppref} {Wz Hz : Mat} {Mh : Mats ℤ}
    (hHz : ∀ j < nD, ∀ v < nV,
      Hz j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    (small : ∀ a r c, |Mh a r c| < 2 ^ 18)
    (rf : Cm.Plain.TP.RF (F := Cb.Gl.E) np (fun j v => ((Hz j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
      (cellsH h L (borderOf y) Mh)) : HeadOrd h L y np Wz x Mh :=
  ⟨small, (matHolds_iff_cells hF hL hl S Z Z2 (fun _ _ r c => Mh (h.NHf + 3) r c)
    (fun _ _ _ => 0) Mh (fun _ _ _ _ => rfl) np x Wz).1
      (matHolds_of_rf hF hL hl S Z Z2 _ _ Mh (fun _ _ _ _ => rfl) hHz rf)⟩

end Link

#print axioms portNo_slotNo
#print axioms stackedH_libOf
#print axioms segM24_iff
#print axioms link24_iff
#print axioms link24_of_ord
#print axioms ord_of_link24
#print axioms ord_of_rf

end OnBytes.Road.Hd
