-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttScl.lean

The hypothesis hsh of "linkA_of_ord" (Johnson/Road/Lane5AttLink.lean), in the verifier's own words:
the shifts of the configuration that the verifier's function fill
(OnBytes/Model/AttentionConfig.lean) makes for group g are the words klSh of the file of scales, and
the library's table of scales that "scalesOf" (Johnson/Road/FormsKeysScl.lean) makes of that file
has these words.

* "fill_sh": what fill returns as the shifts.
* "hsh_of_fill": for groups of four layers and g < 12: the shift of layer 4 g in scalesOf h sc nf is
  the first shift of the configuration.

What is compared with what: the verifier's fill and klSh with the library's Cm.Scales.kap at a table
of these files (scalesOf). Not claimed: that the group has one shift.
-/
import Johnson.Road.Lane5AttShape
import Johnson.Road.FormsKeysScl
import OnBytes.Model.AttentionConfig

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

variable {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
  {lines : List Attention.Line} {g : ℕ} {cf : Attention.Cfg}

/-- The shifts of the configuration that fill returns. -/
theorem fill_sh (hf : Attention.fill P y sc lines g = Except.ok cf) :
    cf.sh = (Array.range y.Lam).map fun lam => sc.klSh (g * y.Lam + lam) := by
  unfold Attention.fill at hf
  obtain ⟨_, _, hf⟩ := bind_ok hf
  obtain ⟨_, _, hf⟩ := bind_ok hf
  have e := Except.ok.inj hf
  subst e
  rfl

/-- **The shift of the group's first layer in the library's table is the configuration's first
shift.** -/
theorem hsh_of_fill (hf : Attention.fill P y sc lines g = Except.ok cf) (hLam : y.Lam = 4)
    (hg : g < 12) (h : Model.Layer.Shape) (nf : Inst.Model.NormPar) :
    ((scalesOf h sc nf).kap (4 * g)).sh = cf.sh.getD 0 0 := by
  have e0 : ((Array.range 4).map fun lam => sc.klSh (g * 4 + lam)).getD 0 0 =
      sc.klSh (g * 4 + 0) := by simp
  rw [← kap_scalesOf h sc nf (show 4 * g < 48 by omega), fill_sh hf, hLam, e0,
    show g * 4 + 0 = 4 * g by omega]
  rfl

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.fill_sh
#print axioms OnBytes.Road.L5.hsh_of_fill
