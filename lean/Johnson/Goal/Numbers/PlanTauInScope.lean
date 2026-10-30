-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanTauInScope.lean: at the public files in the goals' scope the record of
every sub-proof's smallness test in the public part has tau = 128, the number of random combinations
that follows from the library's written setting.

What it is. A step beneath the rows on the rounds that draw matrix entries; no row moves, and no
description of the protocol is named. The planner's test "plan-tau" (`planSmall`,
OnBytes/Params/SubRounds.lean) compares the number of combinations that follows from the setting
with the sub-proof's tau. Here that comparison is shown to hold in scope without the planner: from
the text that makes the public part alone.

  `polWord_tau`, `scan_tau`: the parameter file in scope has the line "tau 128" among its fixed
    lines (`VerifierAndGoals.behindA2`, Ladder/Stored.lean): where the strict scan returns a value, its line
    tau reads 128. The proof follows that of the line D (`polWord_D`, `scan_sizes`,
    Johnson/Goal/PlanValues/ScopeAtPlan.lean). `missA1_tau`, `atA2_tau`, `bytes_tau`: three
    evaluations in Lean's kernel on these fixed lines.
  `record_combinations`: at the written setting (`recordSet`, OnBytes/Params/EntryStagesRecord.lean)
    the number of combinations is 128 in each of the planner's three scopes.
  `tau_in_scope`: in scope, at every o, the line tau of what `publicOfO o` returns reads 128.
  `TauFits X s`: the comparison of "plan-tau" at every sub-proof of X and the setting s, in each
    scope. `PlanTauInScope`, `plan_tau_in_scope`: in scope, at every o, wherever `publicOfO o`
    returns X: `TauFits X recordSet`.
  `plannedAtO_parts`, `proof_set_in_scope`: in scope, at every o and every digest c, where
    `plannedAtO` returns p, the setting in the proof file's sizes is `recordSet` (`scan_frame`;
    `chainsOf_made`, OnBytes/Model/VerifyDerives.lean; `configure_proof_sizes`,
    OnBytes/Plan/PlanListsProof.lean). `plan_tau_at_planned`: so
    `TauFits p.X p.chains.made.sized.proof.set`. Where `plannedAtO` returns a value the planner's
    text has run, and "plan-tau" with it: there this repeats what was asked, and what is new is
    `proof_set_in_scope`.

What of OnBytes/Model/ is used. `polScan`, `PolScan`, `Verify.Public`, `Verify.Planned`,
`Verify.chainsOf`, `Layer.HPlan2`, `Attention.Plan`, `HTailF2` with its field tau, `smallSize`, by
name, in the statements.

Limits. That the planner makes the proof file's first chain under `made.sized.proof.set` is read off
its text (`firstPlan`, OnBytes/Params/DeriveReq.lean); no theorem here says so. No theorem says that
a value is returned at any public files in scope. That the draw of the matrix (`drawMatrixF`,
OnBytes/Model/Tail.lean), or a block of a description, reads the tau of these records is not shown:
that the record whose tau the draw reads is that of X's member at that link stays a premise. Nothing
ties a written plan to these records: that a written plan's own setting is `recordSet`, and that the
rounds "RNG" of the written list were planned at these records, is not shown. Nothing is said of the
columns. Out of scope `publicOfO_tau` and `publicOfO_floor`
(Johnson/Desc/Ok/PlanWritten/TauMade.lean) speak, and nothing here. How many sub-proofs X has is not
said. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.TauMade
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Goal.PlanValues.ScopeAtPlan
import OnBytes.Params.EntryStagesRecord
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind recordLines recordSet rngCombinations Scope)
open Lk6.AtPlan

/-! ## 1. The line tau of the parameter file in scope -/

theorem missA1_tau : (linesOf (bytesOf VerifierAndGoals.behindA1)).all (missB "tau") = true := by
  decide +kernel
theorem atA2_tau : findWord "tau" (linesOf (bytesOf VerifierAndGoals.behindA2)) = some 128 := by
  decide +kernel
theorem bytes_tau : bytesOf "tau" = [0x74, 0x61, 0x75] := by decide +kernel

/-- The line tau is found behind the four lines with free numbers. -/
theorem polWord_tau (v : VerifierAndGoals.FreeLines) : polWord (VerifierAndGoals.policyFile v) "tau" = some 128 := by
  obtain ⟨U, e⟩ := rest_bytes v
  rw [polWord_policy, e, linesOf_append wholeA1, findWord_append_miss "tau" _ _ missA1_tau,
    linesOf_valLine (noFeed_of (by rw [bytes_eps1_lo]; decide)),
    findWord_miss _ (missB_head bytes_tau bytes_eps1_lo (by decide) (by decide) _),
    linesOf_valLine (noFeed_of (by rw [bytes_eps1_hi]; decide)),
    findWord_miss _ (missB_head bytes_tau bytes_eps1_hi (by decide) (by decide) _),
    linesOf_valLine (noFeed_of (by rw [bytes_eps2_lo]; decide)),
    findWord_miss _ (missB_head bytes_tau bytes_eps2_lo (by decide) (by decide) _),
    linesOf_valLine (noFeed_of (by rw [bytes_eps2_hi]; decide)),
    findWord_miss _ (missB_head bytes_tau bytes_eps2_hi (by decide) (by decide) _),
    linesOf_append wholeA2]
  exact findWord_append_some "tau" _ _ 128 atA2_tau

/-- Where the strict scan returns a value on the parameter file at v, its line tau reads 128. -/
theorem scan_tau {v : VerifierAndGoals.FreeLines} {P : PolScan}
    (h : polScan (VerifierAndGoals.policyFile v) = .ok P) : P.h.tau = 128 := by
  have a : P.value "tau" = 128 :=
    Option.some.inj ((ConfigReaders.polWord_of_name h (n := "tau")
      (by simp [valueNames])).symm.trans (polWord_tau v))
  rw [ConfigReaders.polScan_h h]
  exact a

/-! ## 2. The written setting's number of combinations -/

/-- At the written setting the number of combinations is 128 in each of the three scopes. -/
theorem record_combinations (c : Scope) : rngCombinations recordSet c = 128 := by
  cases c <;> decide

/-! ## 3. In scope -/

/-- In scope the line tau of the public part reads 128, at every o. -/
theorem tau_in_scope {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {X : Public}
    (h : publicOfO o Z.pol Z.KL (some Z.lay) = .ok X) : X.P.h.tau = 128 := by
  obtain ⟨v, hv⟩ := inScope_policy hZ
  have hs := publicOfO_scan h
  rw [hv] at hs
  exact scan_tau hs

/-- What the planner's test "plan-tau" compares, at all sub-proofs of a public part X and a setting
s: in each scope the number of combinations that follows from s is the sub-proof's. -/
def TauFits (X : Public) (s : OnBytes.Params.Setting) : Prop :=
  ∀ c : Scope,
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp →
        rngCombinations s c = (smallSize hp.tl).tau) ∧
      (∀ (g : Nat) (a : OnBytes.Attention.Plan), X.A[g]? = some a →
        rngCombinations s c = (smallSize a.seam.tl).tau) ∧
      rngCombinations s c = (smallSize X.H.tl).tau

/-- The statement: in scope, at every o, wherever the public part is made, "plan-tau"'s comparison
holds at the written setting. -/
def PlanTauInScope : Prop :=
  ∀ (o : Nat → ByteArray → ByteArray) (Z : VerifierAndGoals.PublicFiles) (X : Public), VerifierAndGoals.InScope Z = true →
    publicOfO o Z.pol Z.KL (some Z.lay) = .ok X → TauFits X recordSet

/-- **It holds.** -/
theorem plan_tau_in_scope : PlanTauInScope := by
  intro o Z X hZ h c
  have t := tau_in_scope hZ h
  obtain ⟨hG, hA, hH⟩ := publicOfO_tau h
  rw [record_combinations c]
  refine ⟨fun g hp hg => ?_, fun g a hg => ?_, ?_⟩
  · exact ((hG g hp hg).1.trans t).symm
  · exact ((hA g a hg).1.trans t).symm
  · exact (hH.1.trans t).symm

/-- What `plannedAtO` returns holds the public part and the chains that were made of it. -/
theorem plannedAtO_parts {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {c : ByteArray} {p : Planned}
    (h : plannedAtO o pol KL layout c = .ok p) :
    publicOfO o pol KL layout = .ok p.X ∧ chainsOf p.X layout c = .ok p.chains := by
  unfold plannedAtO at h
  obtain ⟨X, eX, h⟩ := exc_bind h
  obtain ⟨ch, ec, h⟩ := exc_bind h
  obtain ⟨b, _, h⟩ := exc_bind h
  cases h
  exact ⟨eX, ec⟩

/-- In scope the setting in the proof file's sizes, under which the planner makes the proof file's
first chain, is the written setting, at every o and every digest c. -/
theorem proof_set_in_scope {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {c : ByteArray} {p : Planned}
    (h : plannedAtO o Z.pol Z.KL (some Z.lay) c = .ok p) :
    p.chains.made.sized.proof.set = recordSet := by
  obtain ⟨hX, hc⟩ := plannedAtO_parts h
  obtain ⟨v, hv⟩ := inScope_policy hZ
  have hs := publicOfO_scan hX
  rw [hv] at hs
  obtain ⟨shapes, hm⟩ := chainsOf_made hc
  rw [scan_frame hs] at hm
  exact (OnBytes.Params.configure_proof_sizes hm).2.1

/-- **In scope, where the planner's text returns a value: "plan-tau"'s comparison holds at the
setting under which the proof file's first chain is planned.** -/
theorem plan_tau_at_planned {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {c : ByteArray} {p : Planned}
    (h : plannedAtO o Z.pol Z.KL (some Z.lay) c = .ok p) :
    TauFits p.X p.chains.made.sized.proof.set := by
  rw [proof_set_in_scope hZ h]
  exact plan_tau_in_scope o Z p.X hZ (plannedAtO_parts h).1

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.missA1_tau
#print axioms VerifiableInference.PlanWritten.atA2_tau
#print axioms VerifiableInference.PlanWritten.bytes_tau
#print axioms VerifiableInference.PlanWritten.polWord_tau
#print axioms VerifiableInference.PlanWritten.scan_tau
#print axioms VerifiableInference.PlanWritten.record_combinations
#print axioms VerifiableInference.PlanWritten.tau_in_scope
#print axioms VerifiableInference.PlanWritten.plan_tau_in_scope
#print axioms VerifiableInference.PlanWritten.plannedAtO_parts
#print axioms VerifiableInference.PlanWritten.proof_set_in_scope
#print axioms VerifiableInference.PlanWritten.plan_tau_at_planned
