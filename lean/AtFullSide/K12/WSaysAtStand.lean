-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WSaysAtStand.lean: what StandRest.saysAt (K12/AtFile/WTable.lean) asks at the last thread:
SaysLeft at one list of words, wordsAtW: the item rows by rows_at_lastThread, the sample rows and the
tie as premises at the record.

  saysLeft_at_stand   SaysLeft at wordsAtW at a stand at number 2

Limits.
- hsamples: samples_at_W_from_threads has it from the three threads. htied: tied_at_stand.
- hE: the test's state on entry is the record's.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind Thr.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointAtLastThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12
open OnBytes.Slice (rdE)
open OnBytes.Means (layoutOf sampleItem)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest.K12.AtFile (SaysLeft)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW rows_at_lastThread)
open ProofFile.Honest.K12.Light (ManyJob plainMany WordsTied)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **At a stand at number 2: SaysLeft at the words of which the thread's item "rows" speaks.** -/
theorem saysLeft_at_stand (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (C : TestCoins) {k : Coins A.B} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (fr : Front X)
    (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds : List Fmt.Drawn)
    (hE : enterOwn st = .ok (M.rec₀ m.st.input fr))
    (hsamples : ∀ G, st.st.groups[st.loc.own]? = some G → sampleItem rdE st.st G.members.toList
      (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)))
    (htied : ∀ G, st.st.groups[st.loc.own]? = some G → WordsTied st.st st.loc.own G
      (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) (layoutOf st.st G)
      (plainMany M m.st.input fr C)) :
    SaysLeft M m.st.input fr C st (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) := by
  have e : M.rec₀ m.st.input fr = { st := st.st, book := st.book, roots := st.roots, g := st.loc.own
                                    pass := .nothing, mask := st.loc.mask } :=
    (Except.ok.inj hE).symm
  have hst : (M.rec₀ m.st.input fr).st = st.st := by rw [e]
  have hg : (M.rec₀ m.st.input fr).g = st.loc.own := by rw [e]
  refine ⟨rows_at_lastThread hd first reads parts w u ds, hsamples, fun G hG => ?_⟩
  rw [hst, hg] at hG ⊢
  exact htied G hG

end AtFullSide.K12

#print axioms AtFullSide.K12.saysLeft_at_stand
