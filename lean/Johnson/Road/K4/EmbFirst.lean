-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbFirst.lean: the last premise, uE, of eight_parts_first
(Johnson/Road/K4/SevenPartsFirst.lean), that the library's claim on the stream that comes in is
worth 0 at the entries yLF, from K4's own claims worth 0 in the first group, on true reads.

Main names:
  `late_emb`: at yLF the late entries that the claim reads are the library's readAt, at the cells
    that the messages hold: emb_reads (Cb/Pv/Lay/End/EmbShare.lean) at embOkF_of
    (Johnson/Road/K4/LateNamesFirst.lean).
  `EmbAsks`: what is asked beside the premises that eight_parts_first has already, ten fields: the
    group is the first; the stream has five limbs; the blocks of the stream are P.nb in number; the
    bits of a feature in its block are P.ls; the point on the blocks has P.gB coordinates; the point
    ZE has P.ls + P.D.lT; the readings of the verifier's two points ZE (two fields) and tkh are the
    library's pa and pb; the hidden value under the slot sVE is the merge round's sent scalar less
    its mask entry. No proof here reads the size of ZE: it is asked so that no coordinate which the
    two fields on ZE read lies behind the point's end, where a reading gives 0.
  `uE_of_front`: the premise uE.
Limits. EmbAsks is a premise: no run is shown at which it holds. All else as in
SevenPartsFirst.lean. Implications in given worlds: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.EmbTies
import Johnson.Road.K4.SevenPartsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Model (World Fork Level)
open OnBytes.Model.Layer (Pub Own)
open Inst.Model (Scl)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {M X0 : Type} (P : FullFPar K M X0)
  (zt : (tailW P).s7.Nx → ℕ → K) (b B sG : ℕ)

/-- At yLF the late entries that the claim reads are the library's reads of the stream's limbs. -/
theorem late_emb (e : (tailW P).s7.Nx) (m : M) :
    ∀ l kh, l < 5 → kh < P.nb →
      yLF P zt b B sG e m (Sum.inr ((lateF (roomF P.D B sG P.nb)).at' (Sum.inr (.x0 l kh)))) =
        Cb.Pv.Lay.End.Gated.readAt P.D (P.rd (P.msg m)) .x0 (stF P e).pa 0 P.ls l 0 kh :=
  fun l kh hl hk =>
    have O := embOkF_of P zt b sG B sG
    emb_reads P.rd P.hrd P.D (lateF (roomF P.D B sG P.nb)) Sum.inr (fmOfF P zt b sG sG e) P.nb P.ls
      (stF P e).pa (P.msg m) (O.hfm e) l kh ⟨hl, hk⟩ (O.hY l hl kh hk)

/-- What uE_of_front asks beside what eight_parts_first asks. -/
structure EmbAsks (X : Rows.Pub34 K) (W : World K) (o : Own) (e : (tailW P).s7.Nx) (m : M) :
    Prop where
  /-- the first group -/
  g0 : o.v.g = 0
  /-- sizes -/
  nl5 : o.v.y.xb.nl = 5
  nb : o.v.y.h.d / o.v.y.S2 = P.nb
  ls : o.v.y.ls = P.ls
  tk : o.H.tkh.size = P.gB
  ze : X.H.ZE.size = P.ls + P.D.lT
  /-- the embedding's point inside a block and at the positions -/
  pa1 : ∀ j, j < P.ls → pt X.ρ X.H.ZE j = (stF P e).pa j
  pa2 : ∀ j, j < P.D.lT → pt X.ρ X.H.ZE (P.ls + j) = (stF P e).pa (P.ls + j)
  /-- its point on the blocks -/
  pb : ∀ j, j < P.gB → pt X.ρ o.H.tkh j = (stF P e).pb j
  /-- the hidden value under the slot -/
  slot : W.slot o.sVE = ((tailW P).y7 e).1.2 (0 : Fin 1) - P.msg m P.mkE

/-- **The claim on the stream that comes in, from K4's own claims in the first group.** -/
theorem uE_of_front (e : (tailW P).s7.Nx) (m : M) (X : Rows.Pub34 K) (W1 : World K) (Mm : Mats K)
    (hR1 : X.ReadsTrue W1 Mm) (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) {Pp : Pub}
    {o : Own} (hv : o.v = X.p.v) {o2 : Level} (h2X : X.hd2 = some o2) (hD : X.D = P.D)
    (hcells : cellsOf P.D (cellsAt X.p.v.y Mm) = P.rd (P.msg m)) (A : EmbAsks P X W1 o e m)
    {rows : Bool} {F0 G : Fork} {fs : Array OnBytes.Model.Aff}
    (h : Desc.First.K4.formsFrontWith rows Pp 0 o F0 = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value X.ρ W1 = 0) :
    Blocks.Form.val (yLF P zt b B sG e m) (embClaim (lateF (roomF P.D B sG P.nb)) Sum.inr
      (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE P.nb P.gB (stF P e).pb) = 0 := by
  obtain ⟨a, ha, -⟩ := emb_mem h
  exact emb_of_front
    (embDict_at X W1 Mm hR1 hscl hv h2X hD hcells A.g0 A.nl5 A.nb A.ls A.pa1 A.pa2 A.tk A.pb P.hnb
      (y := yLF P zt b B sG e m) A.slot (late_emb P zt b B sG e m) ha) h hz

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.late_emb
#print axioms OnBytes.Road.K4.uE_of_front
