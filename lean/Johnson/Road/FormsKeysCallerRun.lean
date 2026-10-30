-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysCallerRun.lean: a run: the public hypotheses of the theorem capstone hold
together at a made-up shape.

Johnson/Road/FormsKeysCaller.lean joins the comparisons of a layer sub-proof's forms, panels and
weight claims with the library's definitions in one theorem, capstone. It has many hypotheses that
speak of public things alone: that the verifier's functions return, tests that the verifier makes,
and equalities of numbers. This file evaluates them in one environment.

The line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof, and it says nothing of other numbers. This file holds no theorem.

What is run. withP of Johnson/Road/FormsKeysRunP.lean calls, at the shape hR8 with the eight lines
of calls pcR8 (Johnson/Road/FormsKeysRun8.lean), in each group of layers, the verifier's own layout,
scalesOf, readsOf, wsLayOf, ropeOf, layTables, panelsA and panelsT, pointsOf and weightClaims, at
made-up points that are tied as the lookup ties them, with the calls' weights that the lookup
computes, and returns an empty list if one of them does not return. The panels' and the claims'
environments are made from one environment there (env), whose list of tables is what layTables
returns (ht). On what they return, callerB evaluates, under the names of capstone's binders:
 hs; hg; hN; hfl for all eight calls; hpad for all eight calls, as an equality of words of the base
 field; hsx, hsy and hzk; he; hHe; hZ, hzt, hm, ha; hs0 and hpt; Zw; hsL; the switch under hlw; h4;
 hc; hcrt and hT; R, as an equality of integers on all layers of the group, positions and pairs of
 channels; what ts_eq concludes from hTS, that the list is 0, 1, 2, 5 (withP makes the list by the
 line hTS itself); hom; hst, with lam by hlam; hw and hparts; hpts and hfun; hl.
The library's sizes are dimV hR8 16 (Johnson/Road/FormsKeysAimV.lean). Three of these hold by the
way this file writes its records, and the run shows nothing of them: R, since the rotary tables of
tbP are written from the verifier's; hHe, since callerB gives the record of what was heard the
weights of the panels' environment; hom, since om is written with 1 at its head.

What is a theorem and is not run: S (switchesR8), Z (sized_dimV), hρ (gl_numerals), htm and hNM
(plan_sizes, Johnson/Road/FormsKeysPlan.lean, for the verifier's own plans; no plan is made here).

What is made up: all numbers of the shape, the scales, every element that stands for a challenge, a
point or a sent value. What is not run: any hypothesis on the world; any other shape; the two
shipped examples' files. No proof is made or checked. The program does not import this file.
-/
import Johnson.Road.FormsKeysCaller
import Johnson.Road.FormsKeysRunZ
import Johnson.Road.FormsKeysAimV

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Heard scalesHeld readsOf layTables tableAsks placePanels stackEnd pointsOf
  funsOf ropeC)
open Inst.Model.FFSeg (fams)

/-- The public hypotheses of capstone, evaluated on what withP has built in one group of layers. -/
def callerB (r : RunP) : List Bool :=
  let y := r.v.y
  let D := dimV hR8 16
  let tb := tbP hR8 r.v.sc r.ce.rope
  let H : Heard := { r.H with fo := { r.H.fo with e := r.pe.e } }
  let lam := ceilLog2 (placePanels r.pans.bl).2
  let om : Array E := #[oneE, Model.ofNat 7]
  [(scalesHeld hR8 r.v.sc).isOk, decide (r.v.g < y.NGr),
   (y.calls.toList.map fun cd => cd.segs.map (·.name)) ==
     ((List.finRange 8).map fun cc => (fams cc).map segName),
   (floorR8 hR8 D).all id, padWordsR8 y tb, padZ y H && r.v.zk == H.fo.zk,
   r.pe.e == (Array.range y.fo.NC).map (Model.Forest.callWeight y.fo H.fo.zy),
   H.fo.e == r.pe.e, testsR8 r.v H,
   (match Model.Forest.shape y.cl y.h.lidb with
    | .ok s0 => (List.range s0.NC).all fun q =>
      (r.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0
    | .error _ => false),
   sizedW (shapeW hR8) D.P, (shapeW hR8).L == hR8.L, hR8.p3, hR8.p4, D.cap == hR8.lidb,
   H.tT.isSome && r.ce.rt == (H.tT.map (·.r)).getD #[],
   (List.range y.Lam).all fun l => (List.range (2 ^ D.lT)).all fun t =>
     (List.range (y.h.dh / 2)).all fun i =>
       ropeC y.h r.v.sc r.ce.rope (r.v.lay l) t i false == tb.C (r.v.g * y.Lam + l) t i &&
         ropeC y.h r.v.sc r.ce.rope (r.v.lay l) t i true == tb.S (r.v.g * y.Lam + l) t i,
   r.TS == [0, 1, 2, 5], om.getD 0 zeroE == oneE,
   (stackEnd y (placePanels r.pans.bl).1 r.ce.rs lam om (elemsR 600 (1 + y.LamM))
     (elemsR 700 r.pans.nextV) (Model.ofNat 801) (Model.ofNat 802)).isSome,
   (match y.calls.mapM r.v.weighedOf with
    | some weighed => ((y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        r.v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2).isSome
    | none => false),
   (match readsOf y with
    | .ok rd =>
      (match layTables (matsR y r.v.g) (tableAsks y rd r.v.g) 0,
        pointsOf y H { r := elemsR 3100 rd.muH } (some { r := elemsR 3200 rd.muH2 }) with
       | some t, some pts => (funsOf y H.fo pts t.2.1).isSome && r.v.tab.length == t.1.length
       | _, _ => false)
    | .error _ => false)]

/- all of them, in both groups of layers -/
#guard withP false hR8 pcR8 callerB == List.replicate 2 (List.replicate 22 true)

end OnBytes.Road
