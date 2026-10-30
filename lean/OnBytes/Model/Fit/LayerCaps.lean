-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/LayerCaps.lean: where the program's reading of the three public files returns, the
numbers from which the own rounds of a layer sub-proof are planned are within the bounds that
OnBytes/Params/Fit/FitSubLayer.lean asks, and so the planning of these rounds keeps a property of
single entries.

Verify.publicOf (OnBytes/Model/VerifyPublic.lean) reads the three public files. Verify.layerNumbers
(OnBytes/Model/VerifySubproofs.lean) fills the record Params.LayerRounds of group g from what it
returns. Five of the record's numbers are arguments of planZero and planJoin: the token bits; the
bits of a block of features with the token bits; the bits of the padded model width less those of a
block; the bits of the number of norm instances; the bits of the number of layers in a group, less
one. The layout's own tests bound the shape's numbers (OnBytes/Model/Fit/LayoutCaps.lean): at most
16 token bits, at most 6 bits of layers, a width of at most 2 ^ 20, a block of at most 16 bits.

Main theorems.
  readsOf_lNI: the bits of the number of norm instances in the tables of reads.
  pubOf_reads, public_reads: the tables of reads in what publicOf returns are readsOf's at its
    layout.
  layer_nums: the five numbers are at most 16, 16, 20, 7 and 5.
  layers_cap: Params.LayerCap (Verify.layerNumbers X.layers hp g), from publicOf's return X, at
    every hp and g.
  layers_keeps: the planning of the rounds of group g's layer sub-proof, as Verify.linkRounds calls
    it, keeps Q at the setting s, if the seven basic routines do (Params.SubBase s Q).

Limits. s and Q are letters. Nothing on the errors that a plan states. Nothing on soundness. The
program does not import this file.


-/
import OnBytes.Model.Fit.LayoutCaps
import OnBytes.Model.Fit.LayerTail
import OnBytes.Params.Fit.FitSubLayer
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Fit

open Fo.BatRows (bindE_ok)
open Fo.Pub (ite_unit_ok ite_pure_ok publicOf_cut)

/-- The bits of the number of norm instances in the tables of reads. -/
theorem readsOf_lNI {y : Layer.Lay} {rd : Layer.Reads} (e : Layer.readsOf y = .ok rd) :
    rd.lNI = ceilLog2 y.NI := by
  unfold Layer.readsOf at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  rfl

/-- Layer.Pub.of takes the tables of reads from readsOf at the layout. -/
theorem pubOf_reads {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : Layer.readsOf L.y = .ok L.rd := by
  unfold Layer.Pub.of at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨rd, hr, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  exact hr

/-- The tables of reads in what publicOf returns are readsOf's at its layout. -/
theorem public_reads {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : Layer.readsOf X.layers.y = .ok X.layers.rd := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, _, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, _, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, _, h⟩ := bindE_ok h
  obtain ⟨seen, _, h⟩ := bindE_ok h
  obtain ⟨owner, _, h⟩ := bindE_ok h
  obtain ⟨H0, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  exact pubOf_reads k4

/-- The five numbers, from the layout's bounds and the tables of reads. -/
theorem layer_nums {h : Layer.Shape} {y : Layer.Lay} {rd : Layer.Reads} (C : LayoutCaps h y)
    (e : Layer.readsOf y = .ok rd) :
    y.h.lt ≤ 16 ∧ y.ls + y.h.lt ≤ 16 ∧ y.lPd - y.ls ≤ 20 ∧ rd.lNI ≤ 7 ∧ y.h.ll - 1 ≤ 5 := by
  have h1 : y.h.lt ≤ 16 := by rw [C.yh]; exact C.lt
  have h2 : y.ls + y.h.lt ≤ 16 := by
    rw [C.yh, C.ls]
    have := C.laLt
    have := C.la
    omega
  have h3 : y.lPd ≤ 20 := by rw [C.lPd]; exact Slice.ceilLog2_le _ _ C.d
  have h4 : rd.lNI ≤ 7 := by
    rw [readsOf_lNI e, C.NI]
    refine Slice.ceilLog2_le _ _ ?_
    have : 2 ^ h.ll ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) C.ll
    omega
  have h5 : y.h.ll - 1 ≤ 5 := by
    rw [C.yh]
    have := C.ll
    omega
  exact ⟨h1, h2, by omega, h4, h5⟩

/-- **The caps of a layer sub-proof's numbers, from publicOf's return.** -/
theorem layers_cap {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL layout = .ok X) (hp : Layer.HPlan2) (g : Nat) :
    Params.LayerCap (Verify.layerNumbers X.layers hp g) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    layer_nums (polLayout_caps (publicOf_cut pol KL layout X hX).1) (public_reads hX)
  have big : (20 : Nat) ≤ 2 ^ 40 := by decide
  exact ⟨Nat.le_trans h1 (by omega), Nat.le_trans h2 (by omega), Nat.le_trans h3 big,
    Nat.le_trans h4 (by omega), Nat.le_trans h5 (by omega)⟩

/-- **The planning of a layer sub-proof's rounds, as Verify.linkRounds calls it, keeps Q.** -/
theorem layers_keeps {s : Params.Setting} {Q : Fmt.Entry → Prop} (B : Params.SubBase s Q)
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) (moment : Nat) :
    Params.Keeps s Q (Params.layerRounds (forestSize X.y.fo) (Verify.layerNumbers X.layers hp g)
      (smallSize hp.tl) hp.nBatched moment) :=
  Params.keeps_layerRounds B _ (layers_cap hX hp g) ⟨layers_small hX g hp hg⟩ _ _

end OnBytes.Model.Fit
