-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5All.lean: all eleven public hypotheses of the way to the reply from the integer
matrices behind each sub-proof, numbered as the verifier's lists number them; from the public part
of a stage and one list of numbers.

The theorem premise_of_ords (Johnson/Road/Lane5Top.lean) asks eleven public things: eight on the
layers and on the output head, three on the shapes of the attention links. The eight are concluded
in Johnson/Road/HeadL5Pub.lean from two hypotheses: the verifier's function publicOf has returned X,
and the numbers of the parameter file are the reference's (PublicAt X.P). The three are concluded in
Johnson/Road/Lane5AttPub.lean from publicOf's line and fourteen numbers (FillRef): eleven of the
parameter file, three of the layers' layout. This file shows that the fourteen follow from the same
two hypotheses, and states all eleven together.

Main theorems: ldh_of_layout (a line of the layers' layout); fillRef_of_at; eleven_of_publicOf.

The letters. The layers' shape is layerShape X.P, their calls X.P.polCalls, their layout X.y, the
scales X.layers.sc; the head's shape is X.hS, its layout X.HLy, at the array X.y.tauFC; the shape of
the attention link of group g is shapeA X g (Johnson/Road/HeadL5Grp.lean).

What is not claimed. That a parameter file has PublicAt: no theorem; a run holds it at the full-size
example's lines (Johnson/Road/Lane5PublicRun.lean). Nothing on the table of
scales being lawful. Nothing on a request or on a proof file. The program does not import this file.
-/
import Johnson.Road.HeadL5Pub
import Johnson.Road.Lane5AttPub

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (NormPar tbRef)

/-- The logarithm of a head's width in a layout is that of the shape's width. -/
theorem ldh_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hy : Model.Layer.layout h pc = .ok y) : y.ldh = ceilLog2 h.dh := by
  unfold Model.Layer.layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  show y0.ldh = ceilLog2 h.dh
  unfold Model.Layer.layoutBase at h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨_, -, h0⟩ := ok_of_bind h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨_, -, h0⟩ := ok_of_bind h0
  obtain ⟨_, -, h0⟩ := ok_of_bind h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨_, -, h0⟩ := ok_of_bind h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at h0
  obtain ⟨silu, fs⟩ := gt
  cases h0
  rfl

/-- The logarithm of 128. -/
theorem ceilLog2_128 : ceilLog2 128 = 7 := by decide +kernel

/-- **Attention's fourteen numbers follow from the one list and the layers' layout.** -/
theorem fillRef_of_at {X : Model.Verify.Public} (A : PublicAt X.P) (H : LayersHeadAt X) :
    L5.FillRef X.P X.y := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := att_of_at A
  have eh : X.y.h = Model.Verify.layerShape X.P := (admitted_of_layout H.lay H.switches.p3).shape
  have L2 := laid2_of_layout H.lay
  have e1 : X.P.h.lt = 10 := A.num 1
  have e2 : X.P.h.lmq = 16 := A.num 18
  have e3 : X.P.h.dh = 128 := A.num 7
  exact {
    lt := e1
    lB := a1
    H := A.num 5
    Gk := A.num 6
    ll := A.num 3
    Sx := a2
    rx := a3
    lmS := a4
    lmh := a5
    lmo := a6
    NAs := by
      rw [a7]
      exact Nat.one_pos
    ldh := by
      rw [ldh_of_layout H.lay]
      show ceilLog2 X.P.h.dh = 7
      rw [e3]
      exact ceilLog2_128
    T := by
      rw [L2.T, eh]
      show 2 ^ X.P.h.lt = 1024
      rw [e1]
      norm_num
    mrow := by
      rw [L2.mrow3, eh]
      show 2 ^ X.P.h.lmq = 65536
      rw [e2]
      norm_num }

/-- **All eleven public hypotheses, from one line and one list of numbers.** nf: any numbers of the
final normalisation; the table of scales is made of the scale file's words and of nf. -/
theorem eleven_of_publicOf {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) (A : PublicAt X.P) (nf : NormPar) :
    LayersHeadAt X ∧ (∀ g, g < 12 → L5.AttSized (shapeA X g)) ∧
      (∀ g, g < 12 →
        ((scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf).kap (4 * g)).sh =
          (shapeA X g).cf.sh.getD 0 0) ∧
      ∀ g, g < 12 → ∀ ι : ℕ, ι < (shapeA X g).u0 →
        (((shapeA X g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι := by
  have H := public_of_publicOf h A
  have F := fillRef_of_at A H
  have K : ∀ g, g < 12 → _ := fun g hg =>
    L5.att_public h H.p4 F (by rw [H.groups]; exact hg) hg (Model.Verify.layerShape X.P) nf
  exact ⟨H, fun g hg => (K g hg).1, fun g hg => (K g hg).2.1, fun g hg => (K g hg).2.2.1⟩

#print axioms fillRef_of_at
#print axioms eleven_of_publicOf

end OnBytes.Road.Hd
