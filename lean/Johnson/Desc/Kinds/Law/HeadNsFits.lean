-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadNsFits.lean: WHERE THE PUBLIC PART OF THE IOP AS WRITTEN IN LEAN IS MADE,
THE OUTPUT HEAD's NUMBER OF HIDDEN SCALARS FITS THE MASK ROW. Theorems. A joint build of the files
of Johnson/Desc/ProofFile/Law/ and Johnson/Desc/Kinds/Law/.

What is proved.
  **head_ns_fits**   ProofFile.pureRoad.pub o pol lay KL = .ok Z implies: the mask code that Z.first.shape
          names is there (zk), and Z.p.X.H.ns + Z.first.shape.answers ≤ zk.ell.
  head_ns_le         so Z.p.X.H.ns ≤ zk.ell.
By built_head_ns (Johnson/Desc/ProofFile/Law/HeadNs.lean: the maker's own public test
linksFit has accepted the segments' structures that it returns, at the parameters read back, and the
last of them bears X.H.ns) and linksFit_ns (Law/LinksFitNs.lean).


Existential quantifier: zk, fixed by Z.first.codes.mask[Z.first.shape.maskCode]? = some zk.
Who spends it. Law/PlanK6NoNs.lean's planK6_of_bound takes Wp.H.ns ≤ b as a premise: at b := zk.ell.
At the full size's written codes zk.ell = 8192.
Not proved here. That the public part is made at any files. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.HeadNs
import Johnson.Desc.Kinds.Law.LinksFitNs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

/-- **The output head's hidden scalars and the answers' pads have room in the mask row.** -/
theorem head_ns_fits {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∃ zk, Z.first.codes.mask[Z.first.shape.maskCode]? = some zk ∧
      Z.p.X.H.ns + Z.first.shape.answers ≤ zk.ell := by
  obtain ⟨hf, pre, L, e, hL⟩ := ProofFile.Law.built_head_ns h
  obtain ⟨zk, hz, hall⟩ := linksFit_ns hf
  have hm : L ∈ Z.p.built.links.toList := by
    rw [e]
    exact List.mem_append_right pre (List.mem_singleton.2 rfl)
  refine ⟨zk, hz, ?_⟩
  rw [← hL]
  exact hall L hm

theorem head_ns_le {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∃ zk, Z.first.codes.mask[Z.first.shape.maskCode]? = some zk ∧ Z.p.X.H.ns ≤ zk.ell := by
  obtain ⟨zk, hz, hle⟩ := head_ns_fits h
  exact ⟨zk, hz, Nat.le_trans (Nat.le_add_right _ _) hle⟩

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.head_ns_fits
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.head_ns_le
