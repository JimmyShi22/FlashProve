-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/BehindSame.lean: the comparison that the proof file's description lays
into its wrapper (ProofFile.sameReply, Johnson/Desc/ProofFile/Frames1.lean: the two states hold the same
heard reply) accepts a state against the same state with the smallness test's part laid anew. It is
the premise hsame of behind_returns (Johnson/Desc/First/TailClaims/BehindChain.lean), at that
comparison. A general law; nothing is evaluated.

  `out_putTl`, `out_putFork`, `out_k8set`: laying the part leaves the state's field out. (The first
    two stand in the library too, to the letter: Johnson/Desc/First/StateOut.lean.)
  **`sameReply_k8set`**: ProofFile.sameReply s (k8PartP.set s q) = true.

Limits. That a description's chain stands under the wrapper at this comparison is not said here.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.K8Claims
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

theorem out_putTl (s : S) (tl : HTailF2) : (s.putTl tl).out = s.out := by
  unfold S.putTl
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem out_putFork (s : S) (F : Fork) : (s.putFork F).out = s.out := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem out_k8set (s : S) (q : K8Part) : (k8PartP.set s q).out = s.out := by
  have e : k8PartP.set s q = (s.putTl q.tl).putFork q.F := rfl
  rw [e, out_putFork, out_putTl]

/-- **The proof file's comparison accepts.** -/
theorem sameReply_k8set (s : S) (q : K8Part) : ProofFile.sameReply s (k8PartP.set s q) = true := by
  unfold ProofFile.sameReply
  rw [out_k8set]
  simp

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.out_k8set
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.sameReply_k8set
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.out_putTl
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.out_putFork
