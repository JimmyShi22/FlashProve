-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadD.lean: the walk that adds all claims of the head (`Head.walk`,
OnBytes/Model/Head.lean) at two requests: `WalkFree` (OnBytes/Flat/LinksFreeHead.lean).

The first four groups of claims do not read the request: up to there the states are equal. From
`claimJoin` on they are alike. `noteConstant` reads the constant of the one equation, which differs,
and passes it to a note alone; a dry run keeps no notes.

Main theorems: the theorem on `Head.noteConstant` under the name that the walk of
OnBytes/Flat/LinksRespTool.lean looks for; `walkFree`.

Not claimed: anything on a run on a view. For proofs only; no module of the program imports this
file.


-/
import OnBytes.Flat.LinksFreeHeadC

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-- The constant of the one equation goes to a note alone, and a dry run keeps no notes. -/
theorem RespOf.OnBytes.Model.Head.noteConstant (group : String) :
    Resp.K (Head.noteConstant group) := by
  refine ⟨by keeps, ?_⟩
  unfold _root_.OnBytes.Model.Head.noteConstant
  refine cmpA.bind' (by keeps) get_rel fun F F' _ => ?_
  exact Cmp.blk.lift ForkAlike (Blk.keeps_note _ _) (relB_note _ _ _)

theorem walkFree : WalkFree := by
  intro R R' tl tl' wo wo' hR htl hwo
  have hR0 := hR
  have hf : FunsAlike R.t.funs R'.t.funs := hR.2.2.2.2
  obtain ⟨cov', w1, f', rfl⟩ := hR.open
  unfold walk
  dsimp only at htl hf ⊢
  iterate 8 (refine fromEq_same (by keeps) fun _ => ?_)
  refine fromEq_of ?_
  refine cmpLA.bind' (by keeps) (liftS_cmpLA (by keeps) (claimJoin_rel hR0)) fun _ _ _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA.bind' (by keeps) (liftS_cmpLA (by keeps) (claimPolicy_rel hR0)) fun _ _ _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA.bind' (by keeps) (liftS_cmpLA (by keeps) (objectsF_rel hf htl)) fun t t' ht => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  rw [← hwo.1]
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  exact cmpLA.pure' ht

end OnBytes.Flat
