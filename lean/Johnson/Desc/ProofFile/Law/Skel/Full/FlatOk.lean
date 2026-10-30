-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/FlatOk.lean: A CLOSED FACT AT THE WRITTEN DATA
(Full/Data.lean), DECIDED BY LEAN's KERNEL, alone in its file: of the 358 written skeletons of the
first chain's flat list every one has `planOk = true`; and what it gives of a list of blocks with
these skeletons.
  `flat_planOk`    the closed fact
  `first_planOk`   where `bs.map skel = flatW`: every block of bs has `planOk = true`
Limits. At written data: that this is the makers' data at the public files is not said here. A
block's `planOk` is a field that its maker lays: what it tests no skeleton says. Nothing on
soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc (Block)

theorem flat_planOk : (flatW.all fun k => k.planOk) = true := by
  decide +kernel

theorem first_planOk {S Cl : Type} {bs : List (Block S Cl)} (h : bs.map skel = flatW) :
    ∀ b ∈ bs, b.planOk = true := by
  intro b hb
  have hm : skel b ∈ flatW := h ▸ List.mem_map_of_mem hb
  exact List.all_eq_true.1 flat_planOk _ hm

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.flat_planOk
#print axioms ProofFile.Sk.Full.first_planOk
