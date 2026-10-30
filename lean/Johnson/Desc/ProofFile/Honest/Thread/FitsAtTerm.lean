-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FitsAtTerm.lean: `Thread.fits` AT THE THREE THREADS OF A RETURN OF
THE MAKER. `fits_head_full`, `fits_shared` and `fits_last` have the test at letters; the one-pass
parts are decided by the kernel (OnePassFull.lean, FitsLaterClosed.lean). Here the letters are the
values of `firstThread`, `sharedThread` and `lastThread`.

  `fits_firstThread`, `fits_sharedThread`, `fits_lastThread`   the three fields `fits`

What stays. `hfix`: each tree available at a border is fixed by the challenges heard there. It is a
condition on the letter `fixed` of the Script and of the two parts. `htk`: each tree in `taken` is
declared as taken over.

What these are. Conditional lemmas on our own definitions. None is one of the library's goals. They
prove nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FitsHeadFull
import Johnson.Desc.ProofFile.Honest.Thread.FitsLater
import Johnson.Desc.ProofFile.Honest.Thread.FitsLaterClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The field `fits₁`.** -/
theorem fits_firstThread (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (hfix : ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      parts.script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b) :
    (firstThread h parts w).fits h.description.first.blocksInOrder.length = true :=
  fits_head_full h.head A.H parts.script _ _ _ _ _ _ _ _ _ w hfix

/-- **The field `fits₂`.** -/
theorem fits_sharedThread {Wt : Type} (h : HeadAtReturn files A) (reads : IndexReaders W₀ Rc)
    (parts : SharedThreadParts A Wt) (w : Common W₀ Rc OnBytes.TableKey)
    (hfix : ∀ b, b ≤ h.description.shared.blocksInOrder.length →
      ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      parts.fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) :
    (sharedThread h reads parts w).fits h.description.shared.blocksInOrder.length = true :=
  SharedThread.fits_shared _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SharedRows.onePass_shared
    (head_planOk h.head) hfix

/-- **The field `fits₃`.** -/
theorem fits_lastThread (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (htk : ∀ σ ∈ parts.taken, ∃ c j, σ = Fmt.TreeSource.taken c j)
    (hfix : ∀ b, b ≤ h.description.second.blocksInOrder.length →
      ∀ σ ∈ (lastThread h first reads parts w).hand b,
      (lastThread h first reads parts w).fixed σ ≤
        (lastThread h first reads parts w).front + roundsTo (lastThread h first reads parts w).bs b) :
    (lastThread h first reads parts w).fits h.description.second.blocksInOrder.length = true :=
  LastThread.fits_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl LastRows.onePass_last
    (head_planOk h.head) htk hfix

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fits_firstThread
#print axioms ProofFile.Honest.FirstThread.fits_sharedThread
#print axioms ProofFile.Honest.FirstThread.fits_lastThread
