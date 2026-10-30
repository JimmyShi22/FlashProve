-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttLink.lean

At the reference sizes: if the attention link of group g is in order, said of the integer matrices
of the verifier's own list ("AttOrd", Johnson/Road/Lane5AttDef.lean), then link 2 g + 1 is in order
in the sense of Johnson/Road/Lane5.lean ("LinkOK") at the library's matrices that are filled from
that list ("attMx", Johnson/Road/Lane5AttMx.lean).

* "kap_rows": every table of scales of the library has 2,307 live rows of the exponential in every
  layer. So nothing is asked of the table of scales on that word.
* "holdsA_iff": the conditions of segment 2 g + 1 at integer matrices M are the second and the third
  clause of the library's relation RFraw, at every integer trace that agrees with M on the valid
  names. It is the library's Cm.Seg.TS.attSpec_holds_iff at segM s (2 g + 1).
* "rfraw_ref": AttOrd S Z gives RFraw at the words of the table s and at the tables tbRef.
* "linkA_gen", "linkA_of_ord": the end, for every shape of the head and every family of segments
  whose segment 2 g + 1 is the library's; and for the plain head.

The hypotheses of the end, beside AttOrd:
  g < 12;
  AttSized S: the shape's numbers are the reference numbers (from the verifier's own call
    shape cf = .ok S and ten numbers of cf and u0: Johnson/Road/Lane5AttShape.lean);
  hsh: the shift of the group's first layer in the table s is the first shift of the shape;
  hE: the verifier's table of exponentials holds the library's refExp at the 2,307 rows (from the
    verifier's own call at S = 12, rx = 8: exp_of_shaped, Johnson/Road/Lane5AttExp.lean).

Not claimed: that a proof file which a verifier accepts has matrices with AttOrd; anything at other
sizes. The program does not import this file.
-/
import Johnson.Road.Lane5AttMx
import Johnson.Road.Lane5AttCongr
import Cm.TargetSegModel

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Inst.Model.All (DA KA SFK DAK)

/-- Every table of scales has 2,307 live rows of the exponential, in every layer. -/
theorem kap_rows (s : Cm.Scales) (L : ℕ) : (s.kap L).expRows = 2307 := by
  unfold Cm.Scales.kap
  split <;> rfl

theorem kap_rows_nat (s : Cm.Scales) (L : ℕ) : (s.kap L).expRows.toNat = 2307 := by
  rw [kap_rows]
  rfl

/-- **The conditions of segment 2 g + 1 are the library's keys and identities**, at every integer
trace that agrees with the matrices on the valid names. -/
theorem holdsA_iff {g : ℕ} (hg : g < 12) (s : Cm.Scales) (x : Instance ppref) (Wz : Mat) (M : Mx)
    (tZ : AttSeg.Raw → ℤ) (ht : Cm.Seg.Agree (Cm.Seg.TS.tMA g M) tZ) :
    (Cm.Seg.TS.segM s (2 * g + 1)).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
        (Cm.Seg.TS.cM M) ↔
      (∀ (c : Fin 4) (Y : ℕ), Y < (DAK s.kap g).used c →
        AttSeg.keyVec (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef
            (AttSeg.castT tZ : AttSeg.Raw → Cb.Gl.F) c Y ∈
          AttSeg.lutSet (AttSeg.lut (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef c)) ∧
      ∀ j : AttSeg.Idn, j.Valid (DAK s.kap g) →
        AttSeg.idnVal (DAK s.kap g) (AttSeg.castT tZ : AttSeg.Raw → Cb.Gl.F) j = 0 := by
  have e : Cm.Seg.TS.segM s (2 * g + 1) = Cm.Seg.TS.attM s g :=
    Cm.Seg.TS.seg_att s (Cm.Seg.TS.attM s) hg
  rw [e]
  exact Cm.Seg.TS.attSpec_holds_iff (scl := SFK s.kap s.nf g) Cm.Seg.TS.fmtRef
    Cm.Seg.keyVec_agree_spec Cm.Seg.idnVal_agree_spec M tZ ht x (Cm.TP.castW Cb.Gl.p Wz)

variable {S : Attention.Shape}

/-- Exp of the table functions that are made from the shape, at a row. -/
theorem tbOf_exp (S : Attention.Shape) (ι : ℕ) :
    (tbOf S).Exp (ι : ℤ) = ((S.Tt.getD ι 0 : ℕ) : ℤ) := rfl

/-- **From the letters of the shape to the letters of the library**: the relation at the words of
the table s and at the tables tbRef. -/
theorem rfraw_ref (hS : AttSized S) {s : Cm.Scales} {g : ℕ}
    (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) {Z : Zs}
    (O : AttOrd S Z) :
    AttSeg.RFraw (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef Cb.Gl.F (cellsA S Z) := by
  have e : dimOf S = DAK s.kap g :=
    (dimOf_ref hS).trans (congrArg AttSeg.Dim.refK (hS.u0.trans (kap_rows_nat s (4 * g)).symm))
  have O2 : AttSeg.RFraw (scl := sclOf S) (dimOf S) tbRef Cb.Gl.F (cellsA S Z) :=
    rfraw_exp (scl := sclOf S) (D := dimOf S) (tb := tbOf S) (tb' := tbRef)
      (fun ι hι => (tbOf_exp S ι).trans (hE ι hι)) O.rel
  have h0 : ((sclOf S).κ 0).sh = ((SFK s.kap s.nf g).κ 0).sh := hsh.symm
  have O3 : AttSeg.RFraw (scl := SFK s.kap s.nf g) (dimOf S) tbRef Cb.Gl.F (cellsA S Z) :=
    Eq.mp (rfraw_sh h0 (dimOf S) tbRef Cb.Gl.F (cellsA S Z)) O2
  rw [e] at O3
  exact O3

/-- The own cells of link 2 g + 1 in attMx are small if the cells of the verifier's rule are. -/
theorem smallA (hS : AttSized S) (g : ℕ) (Z : Zs)
    (hb : ∀ c : AttSeg.Raw, c.Valid DA → |cellsA S Z c| < 2 ^ 18) (h : Cm.Seg.Hd)
    (n : Cm.Seg.Name) (hn : n.Valid h) (hk : n.place.1 = 2 * g + 1) :
    |Cm.Seg.at' (attMx S g Z) n.place| < 2 ^ 18 := by
  cases n with
  | ff g' c =>
    have h2 : 2 * g' = 2 * g + 1 := hk
    omega
  | att g' c =>
    have h2 : 2 * g' + 1 = 2 * g + 1 := hk
    have e : g' = g := by omega
    rw [e, attMx_cell g Z hS c hn.2.1 hn.2.2]
    exact hb c hn.2.1
  | hf φ i =>
    have h2 : 24 = 2 * g + 1 := hk
    omega
  | hd φ i =>
    have h2 : 24 = 2 * g + 1 := hk
    omega
  | hr φ i =>
    have h2 : 24 = 2 * g + 1 := hk
    omega

/-- **Link 2 g + 1 is in order**, for every shape of the head and every family of segments whose
segment 2 g + 1 is the library's. -/
theorem linkA_gen {g : ℕ} (hg : g < 12) (hS : AttSized S) {s : Cm.Scales}
    (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) {Z : Zs}
    (O : AttOrd S Z) (h : Cm.Seg.Hd) (seg : Segs)
    (hseg : seg (2 * g + 1) = Cm.Seg.TS.segM s (2 * g + 1)) (Wz : Mat) (x : Instance ppref) :
    LinkOK h seg Wz x (2 * g + 1) (attMx S g Z) := by
  have Rf := rfraw_ref (s := s) (g := g) hS hsh hE O
  refine linkOK_of_holds
    (fun n hn hk =>
      smallA hS g Z (fun c hc => Rf.1 c (((Cm.lay_valid_refK _).1 c).2 hc)) h n hn hk) ?_
  rw [hseg]
  exact (holdsA_iff hg s x Wz _ _ (agreeA g Z hS)).2 Rf.2

/-- **The plain head: link 2 g + 1 is in order** at the matrices that are filled from the attention
link's own list, if that list meets AttOrd. For every matrix of weights and every request: the
segment reads neither. -/
theorem linkA_of_ord {g : ℕ} (hg : g < 12) (hS : AttSized S) {s : Cm.Scales}
    (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) {Z : Zs}
    (O : AttOrd S Z) (Wz : Mat) (x : Instance ppref) :
    LinkOK Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) Wz x (2 * g + 1) (attMx S g Z) :=
  linkA_gen hg hS hsh hE O _ _ rfl Wz x

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.holdsA_iff
#print axioms OnBytes.Road.L5.rfraw_ref
#print axioms OnBytes.Road.L5.linkA_gen
#print axioms OnBytes.Road.L5.linkA_of_ord
