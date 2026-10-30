-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadKeeps.lean.
What a run of the byte-level lookup routine Forest.pad that returns leaves: corollaries with few
arguments.

Main names, each for Forest.pad calls pub lid F c = .ok ((g, F'), c'):
  `pad_sized'`, `pad_later'`: under Sized F alone: the arrays under the slots have their sizes in
    F', and F' is a later state than F. From Fo.Keeps.pad; no premise on the context.
  `pad_leaves`: under Sized F and Clean c: PadLeft g.shape F F' g, whole.
  Under the same two premises, read off PadLeft: `pad_sized` (its clause fit: Sized F');
    `pad_later` (Later F F', from its clauses next, keep and rest.ns); `pad_next`
    (F'.next = F.next + Forest.elems g.shape); `pad_rest` (the ten fields that are left as they
    were). pad_sized and pad_later say what pad_sized' and pad_later' say without Clean c.
  `pad_clean`: under the same: the run ends on the view with no message open.
  `pad_shapeOf'`: under the same: the record's shape is made of the calls by Forest.shape and
    Forest.pubAsk.
Those under Clean c are read off Fo.hcOut2V.
Does not say: that the routine returns; anything on a dry run but pad_sized' and pad_later'.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLook

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
  {g : Forest.Heard}

theorem pad_sized' (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F) :
    Sized F' := (Keeps.pad calls pub lid F c g F' c' h hF).2

theorem pad_later' (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F) :
    Later F F' := (Keeps.pad calls pub lid F c g F' c' h hF).1

theorem pad_leaves (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) : PadLeft g.shape F F' g :=
  (hcOut2V Cb.Gl.E Model.Reading.gl calls pub lid 5 F F' c c' g h hF hc).2.1

theorem pad_shapeOf' (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) : ShapeOf calls pub lid g.shape :=
  (hcOut2V Cb.Gl.E Model.Reading.gl calls pub lid 5 F F' c c' g h hF hc).1

theorem pad_sized (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) : Sized F' := (pad_leaves h hF hc).fit

theorem pad_later (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) : Later F F' :=
  ⟨by rw [(pad_leaves h hF hc).next]; exact Nat.le_add_right _ _, (pad_leaves h hF hc).rest.2.1,
    (pad_leaves h hF hc).keep⟩

theorem pad_next (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) : F'.next = F.next + Forest.elems g.shape := (pad_leaves h hF hc).next

theorem pad_rest (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) :
    F'.trees = F.trees ∧ F'.ns = F.ns ∧ F'.LS = F.LS ∧ F'.c0 = F.c0 ∧ F'.nClaim = F.nClaim ∧
      F'.theta = F.theta ∧ F'.thetaDrawnF = F.thetaDrawnF ∧ F'.planClaimsF = F.planClaimsF ∧
      F'.kapMapF = F.kapMapF ∧ F'.doorShutF = F.doorShutF := (pad_leaves h hF hc).rest

theorem pad_clean (h : Forest.pad calls pub lid F c = .ok ((g, F'), c')) (hF : Sized F)
    (hc : Clean c) : Clean c' := by
  obtain ⟨-, -, rv, ht, -⟩ :=
    hcOut2V Cb.Gl.E Model.Reading.gl calls pub lid 5 F F' c c' g h hF hc
  exact ht.2.1

end
end Fo
