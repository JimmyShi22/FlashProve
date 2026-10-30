-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSamplesFirstStandPlans.lean: THE TWO SENDINGS OF THE KEY FILE's FIRST CHAIN WHOSE
MESSAGES ARE MEMBERS OF THE OWN TEST's GROUP (the index masks'; W's): THE WRITTEN PLANS `parIK`, `parWK` (E2E/KeyJobW.lean)
AGAINST THE VERIFIER's OWN PLANS `parIdx Xs`, `parW Xs msg` (Johnson/RunOne/KeySendAtDesc.lean), IN SCOPE. Public data alone.

  `groups_told_at_index_masks`, `groups_told_at_vector_w`   at the written declared rounds and the written table of trees
                    the groups that the two sendings' messages are told to join are [[300]] and [[300], []]. By the kernel
  `groups_told_at_own_message`   a control: at the sending between them they are others
  `groups_in_scope`   so they are in scope, at the description's own source
  `index_masks_plan_is_not_the_written_record`, `vector_w_plan_is_not_the_written_record`
                    THE FIND: AS RECORDS THE VERIFIER's PLANS ARE NOT THE WRITTEN ONES: the written ones have groups := []
  `written_index_masks_plan_alike`, `written_vector_w_plan_alike`
                    WHAT DOES HOLD: the notices and the codes are the same (`PlansAlike`, LotOwnSamplesFirstLaw.lean)
  `PlansAlike.trans`, `plans_alike_at_description`   so parts whose two plans have the written notices and codes are alike to
                    the verifier's

Why. `first_chain_members_sample_rows_say` (LotOwnSamplesFirst.lean) asks `PlansAlike` of the parts' plans and the verifier's.
`OwnSenders` (OwnJob.lean) asks of the parts' plans the written notices and codes. It does not ask them to BE `parIK`,
`parWK`: parts that are laid with the description's own plans would not meet that, by the one field groups.

By what. `six_sourced` (E2E/KeyShapeFullSourced.lean), `told_at_return`, `decl_at_return`
(Johnson/AtFull/KeyBack/InScopeNamed.lean). `SF`, `CF` are short names of `keyFull.once.shape`, `keyFull.codes`.

Limits.
- In scope, at the full size. No value of any parts is given here.
- Of the other fields of a plan (place, gp, work, the part's name) nothing is proved here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSamplesFirstLaw
import E2E.KeyJobW
import E2E.KeyShapeFullSourced
import Johnson.RunOne.KeySendAtDesc
import Johnson.AtFull.KeyBack.InScopeNamed
import Johnson.HB.LLHARD.KB4.Told
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes (OracleNotice)
open VerifiableInference.Desc.K1 (Par)
open VerifiableInference.Desc.Key (Source LaterPlaces groupsTold rootsAt rootsBefore lastSendRound)
open Johnson.RunOne.KeySendGood (parIdx parW gIdx gW)
open Johnson.KB4 (toldKeyFull)
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.KeyLay (parIK parWK)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (six_sourced)
open Lk6.AtPlan (keyFull)

/-! ## 1 The groups told, at the written lists -/

/-- The groups that the index masks' message is told to join. By the kernel. -/
theorem groups_told_at_index_masks :
    groupsTold toldKeyFull.1 0 (rootsAt declKeyFull.1 0) = [[300]] := by
  decide +kernel

/-- The groups that the two messages of W's sending are told to join. By the kernel. -/
theorem groups_told_at_vector_w :
    groupsTold toldKeyFull.1 (rootsBefore declKeyFull.1 (lastSendRound declKeyFull.1))
      (rootsAt declKeyFull.1 (lastSendRound declKeyFull.1)) = [[300], []] := by
  decide +kernel

/-- Control: at the sending of the lookups' own message the line says otherwise. -/
theorem groups_told_at_own_message :
    groupsTold toldKeyFull.1 (rootsBefore declKeyFull.1 2) (rootsAt declKeyFull.1 2) ≠ [[300], []] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **In scope the description's own groups at the two sendings.** -/
theorem groups_in_scope (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    gIdx Xs = [[300]] ∧ gW Xs = [[300], []] := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := hs.source
  have eT := Johnson.AtFull.KeyBack.told_at_return scope h0 hm hX
  have eD := Johnson.AtFull.KeyBack.decl_at_return scope h0 hm hX
  unfold gIdx gW
  rw [eT, eD]
  exact ⟨groups_told_at_index_masks, groups_told_at_vector_w⟩

/-! ## 2 The find: not as records -/

/-- **In scope the verifier's plan of the index masks' sending is not the record `parIK`.** -/
theorem index_masks_plan_is_not_the_written_record (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) : parIdx Xs ≠ parIK := by
  intro e
  have h : gIdx Xs = [] := congrArg Par.groups e
  rw [(groups_in_scope hs scope).1] at h
  cases h

/-- **Nor is its plan of W's sending the record `parWK`**, whatever is sent. -/
theorem vector_w_plan_is_not_the_written_record (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (msg : Array OracleNotice) : parW Xs msg ≠ parWK := by
  intro e
  have h : gW Xs = [] := congrArg Par.groups e
  rw [(groups_in_scope hs scope).2] at h
  cases h

/-! ## 3 What holds: the notices and the codes -/

/-- **The written plan of the index masks' sending and the verifier's have the same notices and codes.** -/
theorem written_index_masks_plan_alike (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) : PlansAlike parIK (parIdx Xs) := by
  have h6 := six_sourced hs scope
  have e : Xs.Y.k.oneTime.indexMasks = keyFull.once.input := h6.indexMasks
  have c : Xs.Y.k.oneTime.codes = keyFull.codes := h6.codes
  refine ⟨?_, c.symm⟩
  show (([("the index masks", #[keyFull.once.input])] :
      List (String × Array OracleNotice)).flatMap fun x => x.2.toList).toArray =
    (([("the index masks", #[Xs.Y.k.oneTime.indexMasks])] :
      List (String × Array OracleNotice)).flatMap fun x => x.2.toList).toArray
  rw [e]

/-- **So have the written plan of W's sending and the verifier's**, at what the shape sends with W. -/
theorem written_vector_w_plan_alike (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {msg : Array OracleNotice} (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg) :
    PlansAlike parWK (parW Xs msg) := by
  have h6 := six_sourced hs scope
  have l : Xs.Y.k.oneTime.lin = keyFull.once.shape := h6.lin
  have c : Xs.Y.k.oneTime.codes = keyFull.codes := h6.codes
  have e : OnBytes.linMessageW keyFull.once.shape = some msg := by
    rw [← l]
    exact hm
  refine ⟨?_, c.symm⟩
  show (([("W and what rides with it", (OnBytes.linMessageW keyFull.once.shape).getD #[])] :
      List (String × Array OracleNotice)).flatMap fun x => x.2.toList).toArray =
    (([("W and what rides with it", msg)] :
      List (String × Array OracleNotice)).flatMap fun x => x.2.toList).toArray
  rw [e]
  rfl

/-- Alike to a plan that is alike to a third. -/
theorem PlansAlike.trans {P Q R : Par} (h : PlansAlike P Q) (k : PlansAlike Q R) : PlansAlike P R :=
  ⟨h.sent.trans k.sent, h.codes.trans k.codes⟩

/-- **Two plans with the written notices and codes are alike to the verifier's**, in scope. -/
theorem plans_alike_at_description (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {msg : Array OracleNotice} (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg)
    {indexMasksPlan vectorWPlan : Par} (alikeIndexMasks : PlansAlike indexMasksPlan parIK)
    (alikeVectorW : PlansAlike vectorWPlan parWK) :
    PlansAlike indexMasksPlan (parIdx Xs) ∧ PlansAlike vectorWPlan (parW Xs msg) :=
  ⟨alikeIndexMasks.trans (written_index_masks_plan_alike hs scope),
    alikeVectorW.trans (written_vector_w_plan_alike hs scope hm)⟩

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.groups_told_at_index_masks
#print axioms ProofFile.Honest.K12.AtKey.groups_told_at_vector_w
#print axioms ProofFile.Honest.K12.AtKey.groups_told_at_own_message
#print axioms ProofFile.Honest.K12.AtKey.groups_in_scope
#print axioms ProofFile.Honest.K12.AtKey.index_masks_plan_is_not_the_written_record
#print axioms ProofFile.Honest.K12.AtKey.vector_w_plan_is_not_the_written_record
#print axioms ProofFile.Honest.K12.AtKey.written_index_masks_plan_alike
#print axioms ProofFile.Honest.K12.AtKey.written_vector_w_plan_alike
#print axioms ProofFile.Honest.K12.AtKey.PlansAlike.trans
#print axioms ProofFile.Honest.K12.AtKey.plans_alike_at_description
