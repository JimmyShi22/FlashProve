-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackPub34.lean: the port of the batched sumcheck's two form parts
(Johnson/Road/K4/StackPort.lean) at the library's public record of a layer sub-proof, Pub34
(Johnson/Road/Rows/LayerEnds34.lean), on true reads.

StackPort.lean asks the record SigFits and a handful of the verifier's own returns. A record Pub34
holds these returns as fields, and with "every table of the reads holds what it says of the
matrices Mm" (ReadsTrue) sigFits_of_look concludes SigFits. So here the premises are a
record and its ReadsTrue.

Main names:
  `sigFits_of_pub34`: SigFits at a record's letters, from ReadsTrue.
  `sides_of_pub34`: the placed panels of a record have, member by member, the sides of the library's
    panels.
  `forms_of_pub34`: the record's two forms fin.Alin and fin.Blin are worth the sums, over all
    places, of the place's equality weight times the library's blocks vaOf | vbOf
    (Johnson/Road/K4/StackSides.lean) at the record rPort.
Limits. A record Pub34 is a premise (Johnson/Road/K4/PubOfHearTied.lean makes one at a run of K4's
own text, under premises of its own); so is ReadsTrue. Nothing typed stands in these statements: the
step to Cb/Pv/Lay/At/Inner.lean is StackTyped.lean's and StackPort.lean's. Identities in one world:
nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.PanelSidesAll
import Johnson.Road.K4.StackSides
import Johnson.Road.K4.FormParts
import Johnson.Road.Rows.LayerEnds34
import Johnson.Road.FormsKeysRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (World)
open OnBytes.Model.Layer (placePanels)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW pans)
open Cb.Pv.Lay.At (blk nP)

variable {K : Type} [Field K]

/-- SigFits at a record's letters, on true reads. -/
theorem sigFits_of_pub34 (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K)
    (hRd : X.ReadsTrue Wo Mm) :
    SigFits (scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) X.ρ Wo X.p X.c X.h X.pc X.s X.D X.lk
      (X.c.v.g * X.c.v.y.Lam) (cellsAt X.p.v.y Mm) (cellsOf X.D (cellsAt X.p.v.y Mm))
      (pt X.ρ X.Zp) (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt) (zetaOf X.ρ X.c X.D) X.tb := by
  obtain ⟨T, T2, Ro, hrt⟩ := worlds_of_holds X.ρ Wo X.hy X.S X.hg X.hrd X.hl X.ht X.Z X.hZ X.hzt
    X.h4 X.hcrt X.htm X.hNM X.hpts X.hfun X.hT Mm hRd
  exact sigFits_of_look X.hy X.S X.hs X.hg X.hrd X.hl X.ht X.hρ X.Z X.hc X.hN X.hfl X.hsx X.hsy
    X.hzk X.he X.hZ X.hzt X.hm X.ha X.hs0 X.hpt X.env X.Zw X.hsL X.hlw X.h4 hrt X.R T T2 Ro

/-- The placed panels of a record, member by member. hh: the never-sent vectors in rPort, free; w:
the weights in the library's B sides, free. -/
theorem sides_of_pub34 (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K) (hRd : X.ReadsTrue Wo Mm)
    (hh : ℕ → ℕ → K) (w : ℕ → LW K) :
    letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
    List.Forall₂ (fun b pn => SidesAre X.ρ Wo X.p.v.y X.om X.D
      (rPort X.ρ X.p.v.y X.p.shownT hh X.D (cellsOf X.D (cellsAt X.p.v.y Mm))
        (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt)) X.tb (X.c.v.g * X.c.v.y.Lam) w
      (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt) (X.ρ.val (X.om.getD 1 zeroE)) b pn)
      (placePanels X.pans.bl).1.toList (pans X.D) := by
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  exact placed_sides (sigFits_of_pub34 X Wo Mm hRd) hh w (ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS) X.hp
    X.hcl X.hom X.hst

/-- **The record's two forms, on true reads.** -/
theorem forms_of_pub34 (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K) (hRd : X.ReadsTrue Wo Mm)
    (hh : ℕ → ℕ → K) (w : ℕ → LW K) :
    letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
    X.fin.Alin.value X.ρ Wo = ∑ Y ∈ range (2 ^ X.lam), eqR X.ρ X.c.rs 0 X.lam Y *
        ((pans X.D).map fun pn => blk (pn.wid X.D) (nP X.D pn)
          (vaOf X.D (rPort X.ρ X.p.v.y X.p.shownT hh X.D (cellsOf X.D (cellsAt X.p.v.y Mm))
            (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt)) (zOf X.ρ X.H.fo.zx X.H.fo.zy)
            (X.ρ.val (X.om.getD 1 zeroE)) pn) Y).sum ∧
      X.fin.Blin.value X.ρ Wo = ∑ Y ∈ range (2 ^ X.lam), eqR X.ρ X.c.rs 0 X.lam Y *
        ((pans X.D).map fun pn => blk (pn.wid X.D) (nP X.D pn)
          (vbOf X.D (rPort X.ρ X.p.v.y X.p.shownT hh X.D (cellsOf X.D (cellsAt X.p.v.y Mm))
            (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt)) X.tb (X.c.v.g * X.c.v.y.Lam) w
            (zOf X.ρ X.H.fo.zx X.H.fo.zy) (pt X.ρ X.c.rt) pn) Y).sum := by
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  have F2 := sides_of_pub34 X Wo Mm hRd hh w
  obtain ⟨fa, fb⟩ := forms_ext_own (ρ := X.ρ) (W := Wo) X.hp X.hlam X.hrs X.hst
  refine ⟨?_, ?_⟩
  · rw [fa]
    exact sum_congr rfl fun Y _ => by rw [(vecs_of_sides X.pans.bl F2 Y).1]
  · rw [fb]
    exact sum_congr rfl fun Y _ => by rw [(vecs_of_sides X.pans.bl F2 Y).2]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sigFits_of_pub34
#print axioms OnBytes.Road.K4.forms_of_pub34
