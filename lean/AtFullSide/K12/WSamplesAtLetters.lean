-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WSamplesAtLetters.lean: the premise hsam of saysAt_at_letters, from the hash build's law.

  hsam_at_letters   the sample rows at every stand of thread₃, said₃ at number 2

Limits: NOT IN FRONT OF A LAW OVER COINS.
Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K14.FivesAtTheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K12
open AtFullSide.Honest.TheLetters
open OnBytes.Slice (rdE)
open OnBytes.Means (sampleItem)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The sample rows at every stand at TheLetters' names.** -/
theorem hsam_at_letters (h : HeadAtReturn Z A) {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) :
    ∀ k st m E, ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E →
      ∀ G, st.st.groups[st.loc.own]? = some G → sampleItem rdE st.st G.members.toList
        (wordsAtW h (first h) (reads h) st k m.st.input (m.st.heard ++ [])) :=
  fun _ _ _ _ u => AtFullSide.K14.samples_at_W_at_letters h P R u []

end AtFullSide.K12

#print axioms AtFullSide.K12.hsam_at_letters
