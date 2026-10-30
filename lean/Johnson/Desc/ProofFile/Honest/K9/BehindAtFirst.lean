-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BehindAtFirst.lean: THE STATEMENT "BEHIND" (`BehindS`) AT ALL 75 BORDERS OF THE KIND K9, AT THE FIRST CHAIN's THREAD
OF THE ONLINE PART AS A NAMED TERM (`firstThread`, Honest/Thread/TheFirstThread.lean), at any return A of the maker and the head
at that return. One call of `k9_behindS` (Honest/K9/KeepsBehind.lean) at the thread's own family of clauses (`fHeadJ`): the thread's
letters are passed as they stand in that file, not copied.

  **`k9_behindS_first`**   l < 25, every Said: `BehindS (firstThread h parts w) Said` at 14 l + `IM.nAt l` + 2, + 4, + 6

Limits. The head at the return is a hypothesis. The step's yes is a premise of `BehindS` itself. That the thread's invariant holds
at any run is not proved here. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.KeepsBehind
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **"Behind" at this kind's 75 borders, at the first thread.** -/
theorem k9_behindS_first (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (hl : l < 25) :
    BehindS (firstThread h parts w) Said (14 * l + IM.nAt l + 2) ∧
      BehindS (firstThread h parts w) Said (14 * l + IM.nAt l + 4) ∧
      BehindS (firstThread h parts w) Said (14 * l + IM.nAt l + 6) :=
  k9_behindS h.head A.H parts.script _ _ _ _ _ _ _ _ _ _ w Said
    (fun _ _ _ hK hFo => ⟨⟨⟨⟨⟨hK, hFo⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩) l hl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_behindS_first
