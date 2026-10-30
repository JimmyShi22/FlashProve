-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttPort.lean

The end of Johnson/Road/Lane5AttLink.lean with its public hypotheses in the verifier's own words:
the shape is the one in the plan that the verifier's function "group"
(OnBytes/Model/AttentionConfig.lean) returns for group g, and the library's table of scales is the
one that "scalesOf" (Johnson/Road/FormsKeysScl.lean) makes of the verifier's file of scales.

* "sized_of_group": AttSized of the plan's shape, from group … = .ok X, ten numbers of the shape's
  configuration (CfRef) and 2,307 rows of its table of exponentials.
* "linkA_of_group": link 2 g + 1 is in order at attMx X.S g Z, if Z meets AttOrd X.S Z.

What is left as a hypothesis on public values: CfRef X.S.cf (numbers of the parameter file); hu (the
table has 2,307 rows); hE (it holds the library's refExp). The last two are facts on the closed
function expTable at (12, 8): theorems of Johnson/Road/Lane5AttExp.lean; without them as hypotheses:
linkA_of_group12 (Johnson/Road/Lane5AttPort2.lean).
-/
import Johnson.Road.Lane5AttLink
import Johnson.Road.Lane5AttPlan
import Johnson.Road.Lane5AttScl

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

variable {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales} {midQ : ℕ → ℕ}
  {lines : List Attention.Line} {g : ℕ} {X : Attention.Plan}

/-- The shape in the plan of a group has the reference numbers, if its configuration has. -/
theorem sized_of_group (hG : Attention.group P y sc midQ lines g = Except.ok X)
    (hc : CfRef X.S.cf) (hu : X.S.u0 = 2307) : AttSized X.S := by
  obtain ⟨cf, -, Sh, -, -⟩ := shaped_of_group hG
  rw [Sh.cfg] at hc
  exact sized_of_shaped Sh hc hu

/-- **Link 2 g + 1 is in order, at the shape of the verifier's plan and the table of scales of the
verifier's file.** -/
theorem linkA_of_group (hG : Attention.group P y sc midQ lines g = Except.ok X) (hg : g < 12)
    (hc : CfRef X.S.cf) (hu : X.S.u0 = 2307)
    (hE : ∀ ι : ℕ, ι < X.S.u0 → ((X.S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (h : Model.Layer.Shape) (nf : NormPar) {Z : Zs} (O : AttOrd X.S Z) (Wz : Mat)
    (x : Instance ppref) :
    LinkOK Cm.Seg.Hd.plain (Cm.Seg.TS.segM (scalesOf h sc nf)) Wz x (2 * g + 1)
      (attMx X.S g Z) := by
  have hS := sized_of_group hG hc hu
  obtain ⟨cf, hf, Sh, hL, -⟩ := shaped_of_group hG
  have hsh : ((scalesOf h sc nf).kap (4 * g)).sh = X.S.cf.sh.getD 0 0 := by
    rw [Sh.cfg]
    exact hsh_of_fill hf (hL.symm.trans hS.Lam) hg h nf
  exact linkA_of_ord hg hS hsh hE O Wz x

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.sized_of_group
#print axioms OnBytes.Road.L5.linkA_of_group
