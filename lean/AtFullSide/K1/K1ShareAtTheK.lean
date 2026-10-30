-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/K1ShareAtTheK.lean: the shared "sending" (the kind K1): K1's SHARE AT THE K OF RECORD: K := theK E apart R (E2E/TheKOfRecord.lean: the kinds' rows from one entry a lot and
the later chains' rows). The three memberships of k1Share_whole (K1ShareWhole.lean) become: the entry k1's lot is baseLotS · the entry w's lot is baseWS · the shared chain's two
sendings' rows are among R.shared. One instance; nothing is proved anew. Two theorems; no definition.

  k1_members_at_theK    the three memberships at theK E apart R
  **k1Share_at_theK**       KindShare A (theGOfReturn made h T (theK E apart R)) A.H Rel Th .K1, at every h, T, Rel, Th

Limits. E and R are letters of the K: the two equations and the inclusion are for whoever lays their values to show (by rfl where the entries' lots are ours: both entries
are typed elsewhere). All limits of K1ShareWhole.lean. No property of the protocol is claimed.
-/
import AtFullSide.K1.K1ShareWhole
import E2E.TheKOfRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile (Inst)
open ProofFile.Honest ProofFile.Honest.Term
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheSides AtPublicFiles.TheG

variable {Z : VerifierAndGoals.PublicFiles} {Wt : Type} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The three memberships at the K of record.** -/
theorem k1_members_at_theK (h : HeadAtReturn Z A) (E : TheThirteen (baseFilling Z) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows (baseFilling Z) A.Z A.G)
    (e1 : E.k1.slot = baseLotS) (e2 : E.w.slot = baseWS) (h3 : ∀ r ∈ baseSendings h, r ∈ R.shared) :
    baseLotS ∈ (theK E apart R).lots ∧ baseWS ∈ (theK E apart R).lots ∧
      ∀ r ∈ baseSendings h, r ∈ (theK E apart R).shared :=
  ⟨e1 ▸ mem_theK (e := E.k1) (by simp [TheThirteen.entries]) apart R,
    e2 ▸ mem_theK (e := E.w) (by simp [TheThirteen.entries]) apart R, h3⟩

/-- **K1's SHARE AT THE K OF RECORD.** -/
theorem k1Share_at_theK (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (made : baseMaker Z = .ok A)
    (h : HeadAtReturn Z A) (T : ThreadParts A Wt) (E : TheThirteen (baseFilling Z) A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows (baseFilling Z) A.Z A.G)
    (e1 : E.k1.slot = baseLotS) (e2 : E.w.slot = baseWS) (h3 : ∀ r ∈ baseSendings h, r ∈ R.shared)
    (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R',
      ready A.F A.B ((theGOfReturn made h T (theK E apart R)).prover A.H) w₀ rc x k = .ok R' →
      ThreadsP A.F A.B ((theGOfReturn made h T (theK E apart R)).prover A.H) w₀ rc x k R') :
    KindShare A (theGOfReturn made h T (theK E apart R)) A.H Rel Th .K1 :=
  k1Share_whole hS hL made h T (theK E apart R) (k1_members_at_theK h E apart R e1 e2 h3).1
    (k1_members_at_theK h E apart R e1 e2 h3).2.1 (k1_members_at_theK h E apart R e1 e2 h3).2.2 Rel Th

end AtFullSide.K1

#print axioms AtFullSide.K1.k1_members_at_theK
#print axioms AtFullSide.K1.k1Share_at_theK
