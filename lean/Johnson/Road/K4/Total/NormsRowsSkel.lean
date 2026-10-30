-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/NormsRowsSkel.lean: TWO OF THE PARTS OF THE LAW "behind K4's hearing its two
runs of claims return" (Johnson/Road/K4/Total/Returns.lean): the listings normsForms (group 2, the
sums of squares) and rowsForms (groups 4 to 6, the norms' rows) of OnBytes/Desc/First/K4/Claims.lean
return at two records of one skeleton, or at neither.

  `norms_skel : NormsSkel`. ONE public record P stands on both sides. What the listing's return
    reads: P's layout (the tensor "xs", a test on three numbers, every index) and P's reads (lNI, in
    the length that hiTab wants); the first entries of two families of tables; THE LENGTH of the
    challenge vector of the sums of squares' sumcheck (hiTab); whether U3at returns. The
    coefficients (the equality table's entries, the powers of gam) are read with a default: no
    Option.
  `rows_skel : RowsSkel`. What it reads: the environment's layout (the number of norms) and whether
    the digits' rows at the two token points are found (digitsAt). What was heard goes into the
    forms alone.
No value that a prover sends or the verifier draws is read for a return in either.
No new argument: a walk of each do-block with the lemmas of Total/IsSomeKit.lean and
Total/SkelReaders.lean.
Limits. Congruences: neither says that a listing returns anywhere. Nothing on what a form is worth.
K04_law, the law of K4's block itself, IS NOT PROVED. Met through Lean at no member. Nothing on
soundness.


-/
import Johnson.Road.K4.Total.SkelReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own)

/-- **Group 2.** -/
theorem norms_skel : NormsSkel := by
  intro P o o₀ S
  unfold normsForms
  simp only [Option.bind_eq_bind, Option.pure_def]
  rw [tabAt_skel S.v, tabAt_skel S.v]
  refine bind_same _ fun txs => bind_same _ fun _ => bind_same _ fun tI => bind_same _ fun tA =>
    bind_both (hiTab_same S.wpl _ _) fun e e' => bind_both (sumForms_same _ fun x _ => ?_)
      fun _ _ => rfl
  rw [Option.isSome_map, Option.isSome_map]
  split
  · exact U3at_skel S.v _ _
  · exact U3at_skel S.v _ _

/-- **Groups 4 to 6.** -/
theorem rows_skel : RowsSkel := by
  intro o o₀ S
  unfold rowsForms
  simp only [Option.bind_eq_bind, Option.pure_def]
  rw [S.v.y]
  refine bind_both (mapM_same _ fun i _ => ?_) fun _ _ =>
    bind_both (mapM_same _ fun i _ => digitsAt_skel S.v _ _) fun _ _ => rfl
  rw [Option.isSome_map, Option.isSome_map]
  exact digitsAt_skel S.v _ _

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.norms_skel
#print axioms OnBytes.Desc.First.K4.Total.rows_skel
