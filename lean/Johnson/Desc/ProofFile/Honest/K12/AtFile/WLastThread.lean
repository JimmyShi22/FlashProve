-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WLastThread.lean: the five statements at the last chain's proximity
test at the thread that the library lays: `lastThread` (Honest/Thread/TheFirstThread.lean), at a return of
the maker.

  `five_at_lastThread`   `FiveAt` at number 2, from `LetterAtW`, `StandAtW` and the two letters
                   `parts.rides`, `parts.keeps` under the stand and the step. `hPL` by `fillZ_is`, `hB`
                   by `book_laid`, the order by `tidy_behind`

Limits.
- `LetterAtW` and `StandAtW` are premises here: `letter_at_filling` (WFilling.lean) has the first at the
  base filling's job; `StandAtW` holds what stays open.
- NOT IN FRONT OF A LAW OVER COINS.
- That a stand is reached is not said; where none is, the five say nothing.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WHanded
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFiveAt
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import AtFullSide.K12.LettersTwelve

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (lastPlaces)
open ProofFile.Honest.K12.AtProof (fourOf idleT12)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.LastThread (lettersLast)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread
  lastWitness)
open ToldDesc (ownAt)

variable {W₀ Rc Tr X₀ X : Type}

/-- **The five at the thread that the library lays.** -/
theorem five_at_lastThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
    (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : ℕ → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (hp : M.p = (fourOf h.places).W) (f : Addr × ℕ)
    (hfr : M.fresh = some f) (hl : M.mems.length = 3) (hd : M.trees.map (·.1) = [13, 22, 22])
    (H₀ : LetterAtW h.description (lastThread h first reads parts w) 2 M enterOwn leaveOwn
      ((ownAt h.places).retype : Block S₃ ProofFile.Cl) idleT12)
    (S : StandAtW h.description (lastThread h first reads parts w) Said 2 M)
    (hnext : ∀ k s m E ds y cols s', ThrS (lastThread h first reads parts w) Said 2 k s m E →
      drawsFit ((ownAt h.places).retype : Block S₃ ProofFile.Cl).rounds ds = true →
      (lastThread h first reads parts w).Stepped ((ownAt h.places).retype : Block S₃ ProofFile.Cl) k s m E
        ds y cols s' →
      parts.rides 3 y.2.st.input s' ∧ parts.keeps ⟨3, none, 2, .K12⟩ s s')
    (fl : ℕ → S₃ → List Fmt.Drawn → Option String) :
    FiveAt (lastThread h first reads parts w) Said fl 2 := by
  obtain ⟨filling, hret⟩ := h.returned
  have hplan : (VerifiableInference.Desc.K12.proximityTestKind guardedProximityTestParts M.toRun.toTest.p : Block T12 Unit).planOk =
      true := (public_head_W h.head.toAtMg M hp (by rw [hfr]; rfl)).2.2.1
  refine five_at_W A.H h.sharedNumbers parts.meaning h.lastMeaning h.lastForm
    (fun s => OnBytes.Means.InOrder s.st) parts.taken parts.ends (lastWitness h first reads)
    parts.table parts.fixed 0 h.description.t₁ h.description.t₂
    (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
    (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w h.head.toAtMg
    (AtFullSide.K12.book_laid h.head hret) Said M hp f hfr hl hd (fillZ_is _ _) H₀ S ?_ fl
  intro k s m E ds y cols s' u hd' hS
  obtain ⟨hr, hk⟩ := hnext k s m E ds y cols s' u hd' hS
  obtain ⟨⟨-, -, hform, -⟩, -⟩ := u
  obtain ⟨f', o', -, -, h2⟩ := shape_of_form (lettersLast A.Z h.places h.firstChain A.H h.sharedNumbers
    parts.meaning h.lastMeaning h.lastForm (fun s => OnBytes.Means.InOrder s.st) parts.taken parts.ends
    (lastWitness h first reads) parts.table parts.fixed 0 h.description.t₁ h.description.t₂
    (ProofFile.Honest.ReadyInput h.description A.H) parts.rides
    (ProofFile.Honest.K14.kpSecond (ToldDesc.p14At A.Z) parts.keeps) w) (fillZ_is _ _) hform
  obtain ⟨-, -, -, hdec⟩ := VerifiableInference.Desc.step_inv _ _ _ _ _ _ _ hS.2
  refine ⟨(tidy_behind H₀.seat hplan h2 hdec).inOrder, hr, fun q hq => ?_⟩
  have e : lastPlaces[2]? = some ⟨3, none, 2, .K12⟩ := rfl
  obtain rfl := Option.some.inj (hq.symm.trans e)
  show (if (⟨3, none, 2, .K12⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
  rw [if_neg (by decide)]
  exact hk

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.five_at_lastThread
