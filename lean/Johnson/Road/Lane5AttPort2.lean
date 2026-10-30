-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttPort2.lean

"linkA_of_group" (Johnson/Road/Lane5AttPort.lean) without its two hypotheses on the table of
exponentials: they follow from S = 12 and rx = 8 (Johnson/Road/Lane5AttExp.lean).

What is left as a hypothesis on public values: twelve numbers of the configuration in the plan that
the verifier's function group returns (CfRef, S = 12, rx = 8).
-/
import Johnson.Road.Lane5AttPort
import Johnson.Road.Lane5AttExp

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-- **Link 2 g + 1 is in order**: the shape is the one in the verifier's plan, the table of scales
is made of the verifier's file, and twelve numbers of the configuration are the reference
numbers. -/
theorem linkA_of_group12 {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}
    (hG : Attention.group P y sc midQ lines g = Except.ok X) (hg : g < 12) (hc : CfRef X.S.cf)
    (h12 : X.S.cf.S = 12) (h8 : X.S.cf.rx = 8) (h : Model.Layer.Shape) (nf : NormPar) {Z : Zs}
    (O : AttOrd X.S Z) (Wz : Mat) (x : Instance ppref) :
    LinkOK Cm.Seg.Hd.plain (Cm.Seg.TS.segM (scalesOf h sc nf)) Wz x (2 * g + 1)
      (attMx X.S g Z) := by
  obtain ⟨cf, -, Sh, -, -⟩ := shaped_of_group hG
  rw [Sh.cfg] at h12 h8
  obtain ⟨hu, hE⟩ := exp_of_shaped Sh h12 h8
  exact linkA_of_group hG hg hc hu hE h nf O Wz x

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.linkA_of_group12
