-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K3X/HeadForEntry.lean: the two equations on the output head's lookup that the entry
test on the head's calls still asks (`headEntry_zFull_of`, Johnson/AtFull/Entry/K3AtX0.lean), at
what the public part's maker returns at the library's written copy of the full-size public files
(`VerifierAndGoals.storedPublicFiles`, as Ladder/Stored.lean spells it). A joining: calls alone.

  `head_laid_zFull`: the head's layout in the maker's value is one that `Head.layout` returns at
    the full size's written numbers (`LaidW`, Johnson/AtFull/Head/LayoutAtFull.lean).
  **`head_calls_zFull`**: the head's six calls, their tables stripped, are `callsHead`.
  **`head_pub_zFull`**: the lookup's numbers of padding keys are `pubHead`.
Each at whatever letter X₀ the maker `publicOfO`, at the second hash function, returns there.

By: the maker's return names its value's parts by letters, each with its own maker's equation
(`publicOfO_zFull_of_rest`, Johnson/AtFull/Public/Join.lean): the third of these is the first
statement. The two equations at every such layout: `head_two`
(Johnson/AtFull/K3X/HeadSegment.lean).

Limits. UNDER hsz : the written layout file has 224975 bytes, WHICH IS NOT PAID HERE. No Lean
statement ties `VerifierAndGoals.storedPublicFiles` to the files of a release's example folder; the example's weights are
synthetic. Equations on public data: no proof is read. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.K3X.HeadSegment
import Johnson.AtFull.Public.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO)
open _root_.AtFull.Head (LaidW)

/-- **The head's layout in the maker's value.** -/
theorem head_laid_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : LaidW (.ok X₀.HLy) := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, -, -, ⟨e3, -, e3L⟩, -, -, -, -, -, -, -,
    hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain rfl : _ = X₀ := Except.ok.inj (hX'.symm.trans hX)
  show LaidW (.ok HLy)
  rw [← e3]
  exact e3L

/-- **The head's six calls, their tables stripped.** -/
theorem head_calls_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    X₀.HLy.cl.map Johnson.AtFull.ProofRows.K3.strip = Johnson.AtFull.ProofRows.K3.callsHead :=
  (head_two (head_laid_zFull hsz hX)).1

/-- **The lookup's numbers of padding keys.** -/
theorem head_pub_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : X₀.HLy.fs.pub = Johnson.AtFull.ProofRows.K3.pubHead :=
  (head_two (head_laid_zFull hsz hX)).2

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.head_laid_zFull
#print axioms Johnson.AtFull.K3X.head_calls_zFull
#print axioms Johnson.AtFull.K3X.head_pub_zFull
