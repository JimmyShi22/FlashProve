-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttKeysAt.lean.
The attention sub-proof: the key forms that its routine hands to the lookup's join have, under the
rule, the values of the key vectors' extensions: in the words in which the lookup's tie asks it
(Fo.KeysAt).

States:
  ofList_rdL: an array of the byte-level field, read as a list and then as a point, is the library's
    reading of the array.
  pub_size: under the public premises of its kind a call's key point has the call's n coordinates.
  att_keysAt: under Fo.RuleA: Fo.KeysAt, for the record of key forms Fo.joinsA h NC, the key vectors
    kvA and the calls' key points of the lookup's record, read.
Limit: Fo.RuleA is a hypothesis (OnBytes/Tie/Pv/Lookup/Ends/FoAttKeys.lean); no statement of this
library concludes it.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKeys
import OnBytes.Tie.Pv.Lookup.Ends.FoKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Attention OnBytes.Ends OnBytes.Ends.A

theorem ofList_rdL (z : Array E) : Blocks.ofList (rdL Reading.gl z) = readV z := by
  funext t
  exact (rdL_getD Reading.gl z t).symm

theorem pub_size {h : Attention.Heard} {q : ℕ} {c : ACall} {b' : ℕ} (hp : PubOf h q c b') :
    (h.g.zk.getD q #[]).size = c.call.n := by
  rcases hp with ⟨_, C⟩ | ⟨_, _, C⟩ | ⟨_, _, C⟩ | ⟨_, _, C⟩ <;> exact C.size

/-- The key forms have the values of the key vectors' extensions. -/
theorem att_keysAt (W : World Cb.Gl.E) (cell : NameA → Cb.Gl.E) (h : Attention.Heard) (NC b' : ℕ)
    (hR : RuleA W cell h NC b') :
    KeysAt Reading.gl W NC (joinsA h NC).kf (kvA h.S h.g.shape cell)
      fun q => rdL Reading.gl (h.g.zk.getD q #[]) :=
  keysAt_of_ext Reading.gl W NC _ _ _ fun q hq => by
    obtain ⟨c, hc, e⟩ := att_keys W cell h NC b' hR q hq
    obtain ⟨c', hc', hp⟩ := hR.pub q hq
    obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
    rw [kf_at h NC q hq, e, ofList_rdL]
    congr 1
    unfold rdL
    rw [List.length_map, Array.length_toList, pub_size hp]

end Fo
