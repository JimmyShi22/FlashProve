-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysAimV.lean: the hypotheses of the theorems on the weight claims, in the words
of the verifier's caller, and sizes of the library that meet them.

The records ClaimFits (Johnson/Road/FormsKeysClaim.lean) and AimFits
(Johnson/Road/FormsKeysAim.lean) speak of a shape s of the weights and of sizes D of the library.
The verifier's public part (publicOf and polLayout in OnBytes/Model/VerifyPublic.lean) makes the
shape of a layer sub-proof and the shape of the weights from one scan Q of the parameter file:
layerShape Q and weightShape Q y. This file states the records' hypotheses on s for that shape, and
gives sizes that meet them.

What is compared with what: the verifier's two shapes, made from one scan, against the library's
parameters.

Main definitions: dimV. Main theorems.
 - sizedW_of_layout: if the layout of the layer sub-proof is what layout returns on layerShape Q,
   the library's sizes agree with that shape, and they have the file's number of layers and its
   vocabulary, then weightShape Q y agrees with the library's parameters (SizedW).
 - sized_dimV, sized2_dimV: the sizes dimV h V agree with the shape h (Sized; Sized2 under three
   equations on the shape), have the verifier's cap on a tree's depth, the shape's number of layers
   and the vocabulary V.
 - sizedW_dimV: so weightShape Q y agrees with the parameters of dimV (layerShape Q) Q.h.V.
 - aimFits_public: the record AimFits from the caller's own calls.

Why dimV. The sizes dimOf h of Johnson/Road/FormsKeysFits.lean, and dimA h and dimC h that are made
from them, have the vocabulary 0. SizedW then asks the vocabulary 0 of the shape of the weights. By
the text of wsLayOf (OnBytes/Model/Weights.lean) it refuses such a shape; no theorem here shows
that.

The hypotheses of aimFits_public are calls of the verifier's public part that return, the switches,
that g is the number of a group, and of the library's sizes: Sized, the number of layers, the
vocabulary. The last three are met by dimV (sized_dimV). That the calls return is run at both
public examples in Johnson/Road/FormsKeysRunWK.lean. That the environment of a layer sub-proof's
claims carries that layout y and that layout of the weights is by reading alone (Pub.of in
OnBytes/Model/LayerPlan.lean and the check of a layer sub-proof in OnBytes/Model/Layer.lean).

What is not claimed: see Johnson/Road/FormsKeysAim.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysAim
import Johnson.Road.FormsKeysCap
import OnBytes.Model.VerifyPublic

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Reading PolScan wsLayOf)
open OnBytes.Model.Layer (ClaimEnv Lay layout)
open OnBytes.Model.Verify (layerShape weightShape)
open Inst.Model.FFSeg (Dim lamS)

variable {K : Type} [Field K]

/-! ## The shape of the weights, as the verifier's caller makes it -/

/-- The shape of the weights that the verifier's public part hands to wsLayOf agrees with the
library's parameters. Asked: y is the layout that layout returns on the shape made from the same
scan; there are routed experts; the library's sizes agree with that shape; they have the file's
number of layers and its vocabulary. Beside: that shape of the weights has the layer sub-proof's
number of layers. -/
theorem sizedW_of_layout {Q : PolScan} {pc : List (List String)} {y : Lay}
    (hy : layout (layerShape Q) pc = .ok y) (hp3 : (layerShape Q).p3 = true) {D : Dim}
    (Z : Sized (layerShape Q) D) (hL : D.P.layers = Q.h.L) (hV : D.P.V = Q.h.V) :
    SizedW (weightShape Q y) D.P ∧ (weightShape Q y).L = (layerShape Q).L := by
  have A := admitted_of_layout hy hp3
  have sh := A.shape
  refine ⟨⟨hL.symm, Z.d.symm, Z.ch.symm, ?_, ?_, Z.f.symm, Z.fe.symm, Z.nexp.symm, hV.symm⟩, rfl⟩
  · show y.dq = D.P.nq * D.P.ch
    rw [A.laid.dq, sh, Z.nq, Z.ch]
  · show y.dkv = D.P.nkv * D.P.ch
    rw [A.laid.dkv, sh, Z.nkv, Z.ch]

/-! ## Sizes of the library with a vocabulary -/

/-- The sizes dimC h (Johnson/Road/FormsKeysCap.lean) with the vocabulary V. -/
def dimV (h : Model.Layer.Shape) (V : ℕ) : Dim :=
  { dimC h with P := { (dimC h).P with V := V } }

/-- They agree with the shape, have the verifier's cap on a tree's depth, the shape's number of
layers and the vocabulary V. -/
theorem sized_dimV (h : Model.Layer.Shape) (V : ℕ) :
    Sized h (dimV h V) ∧ (dimV h V).cap = h.lidb ∧ (dimV h V).P.layers = h.L ∧
      (dimV h V).P.V = V :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

/-- They meet the second record of sizes for every shape in which af, qa and the stream have columns
of one height and ad is in one part. -/
theorem sized2_dimV {h : Model.Layer.Shape} (V : ℕ) (hq : h.lmq = h.lmaf) (hx : h.lmx = h.lmaf)
    (hd : h.NAd = 1) : Sized2 h (dimV h V) :=
  ⟨rfl, by rw [hq]; rfl, by rw [hx]; rfl, rfl, rfl, rfl, hd⟩

/-- The caller's shape of the weights agrees with the parameters of these sizes, at the file's
vocabulary. -/
theorem sizedW_dimV {Q : PolScan} {pc : List (List String)} {y : Lay}
    (hy : layout (layerShape Q) pc = .ok y) (hp3 : (layerShape Q).p3 = true) :
    SizedW (weightShape Q y) (dimV (layerShape Q) Q.h.V).P :=
  (sizedW_of_layout hy hp3 (sized_dimV (layerShape Q) Q.h.V).1 rfl rfl).1

/-! ## The record, from the caller's own calls -/

/-- The record AimFits in the words of the verifier's public part: the layout of the layer sub-proof
and the layout of the weights are what layout and wsLayOf return on the shapes made from one scan Q,
with the scan's lines of calls and its number of column bits. Asked beside: the switches; g is the
number of a group; the library's sizes agree with the shape and have the file's number of layers and
its vocabulary. ζ is the batched sumcheck's point in the library's order. -/
theorem aimFits_public {ρ : Reading K} {c : ClaimEnv} {Q : PolScan}
    (hy : layout (layerShape Q) Q.polCalls = .ok c.v.y) (S : Switches (layerShape Q))
    (hl : wsLayOf (weightShape Q c.v.y) c.v.y.h.p3 Q.lkW = .ok c.wsLay)
    (hg : c.v.g < c.v.y.NGr) {D : Dim} (Z : Sized (layerShape Q) D) (hL : D.P.layers = Q.h.L)
    (hV : D.P.V = Q.h.V) :
    AimFits ρ c (layerShape Q) Q.polCalls (weightShape Q c.v.y) D Q.lkW (c.v.g * c.v.y.Lam)
      (zetaOf ρ c D) := by
  obtain ⟨Zw, hsL⟩ := sizedW_of_layout hy S.p3 Z hL hV
  have h3 : c.v.y.h.p3 = true := by
    rw [(admitted_of_layout hy S.p3).shape]
    exact S.p3
  rw [h3] at hl
  exact aimFits_of_layout hy S Z hg Zw hsL hl fun _ _ => rfl

#print axioms sizedW_of_layout
#print axioms sized_dimV
#print axioms sized2_dimV
#print axioms sizedW_dimV
#print axioms aimFits_public

end OnBytes.Road
