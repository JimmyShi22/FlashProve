-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineLastWide.lean: THE FIELD `wide` OF `LastLeft` (E2E/OfflineLastFields.lean), in that field's own text: the premise hwide of
`last_laid` (E2E/KeyLastLaid.lean) at the last chain's thread as a term (`lastThread`, E2E/OfflineLastTerms.lean): each tree that the
last chain's proximity test takes over from an earlier chain is at hand at the border 2, and the thread's table
behind it has the declared width.

  `value_idx_numbers`   the place, codes, notices and table sent along of the index masks' sending at the offline value
  `value_w_numbers`     the same of W's sending
  `last_wide`           **the field**

By `hwide_own`, `idx_words`, `w_words`, `omega_words` (E2E/OfflineWidthsOfTreesSentBeforeTestAt.lean), at the first chain's tables `tbH` and the shared
chain's `tableKey`. In scope, at the written book. All the join's letters are free; no premise on the input.

Limits. Widths alone: nothing on what a table holds. Nothing on any property.
-/
import E2E.OfflineLastTerms
import E2E.OfflineWidthsOfTreesSentBeforeTestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.Light (askOf)
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (randK14)
open AtPublicFiles.KeyLay (jobKWAt parIK parWK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub OneFull idxPlace wPlace rideW)
open AtPublicFiles.KeyValues (oneOf batchedRowsSending)
open AtPublicFiles.FirstH (LaterFill tbH)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles five_sourced)
open AtPublicFiles.AtFiles.HonestTerm
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles}

/-- The numbers of the index masks' sending at the offline value, in scope. -/
theorem value_idx_numbers {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) :
    (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).idx.P.place = idxPlace ∧
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).idx.P.codes = parIK.codes ∧
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).idx.P.sent = parIK.sent ∧
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).idx.ride = fun _ => none := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf d.source) := ⟨ec, ei, er, el⟩
  have e : parIK.sent = #[keyFull.once.input] := by
    show ([("the index masks", #[keyFull.once.input])].flatMap (·.2.toList)).toArray = _
    simp
  refine ⟨rfl, one.codes, ?_, rfl⟩
  rw [e, ← one.idx]
  exact AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _

/-- The numbers of W's sending at the offline value, in scope. -/
theorem value_w_numbers {d : OfflineDescription}
    (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true) :
    (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).w.P.place = wPlace ∧
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).w.P.codes = parWK.codes ∧
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).w.P.sent = parWK.sent ∧
      (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).w.ride = rideW := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf d.source) := ⟨ec, ei, er, el⟩
  have e : parWK.sent = (OnBytes.linMessageW keyFull.once.shape).getD #[] := by
    show ([("W and what rides with it", (OnBytes.linMessageW keyFull.once.shape).getD #[])].flatMap
      (·.2.toList)).toArray = _
    simp
  obtain ⟨wm, hw⟩ : ∃ wm, OnBytes.linMessageW keyFull.once.shape = some wm := by
    have h := AtPublicFiles.KeyBook.rides_full.2.2
    cases hq : OnBytes.linMessageW keyFull.once.shape with
    | none => rw [hq] at h; cases h
    | some wm => exact ⟨wm, rfl⟩
  have hl : OnBytes.linMessageW d.source.Y.k.oneTime.lin = some wm := by rw [one.lin]; exact hw
  obtain ⟨h1, h2, h3, h4⟩ :
      (batchedRowsSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixReader d.source d.numbers).P.codes = keyFull.codes ∧
        (batchedRowsSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixReader d.source d.numbers).P.sent =
          (OnBytes.linMessageW keyFull.once.shape).getD #[] ∧
        (batchedRowsSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixReader d.source d.numbers).P.place = wPlace ∧
        (batchedRowsSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixReader d.source d.numbers).ride = rideW := by
    unfold batchedRowsSending AtPublicFiles.Key.wJob
    rw [hl, hw]
    exact ⟨one.codes, AtPublicFiles.KeyBook.sendingPar_sent _ _ _ _ _, rfl, rfl⟩
  exact ⟨h3, h1, h2.trans e.symm, h4⟩

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (d : OfflineDescription) (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **The trees that the last chain's test takes over are at hand at the border 2, at their declared widths.** -/
theorem last_wide (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) :
    ∀ w x (k : Coins (keyBook K₀)) (m : Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
    ∀ d' ∈ (proximityTestKind guardedProximityTestParts (jobKWAt d.source d.numbers d.later (offlineSenders (files := Z) d).idx
                                       (offlineSenders (files := Z) d).w (offlineSenders (files := Z) d).send id
                                       (askOf (offlineSenders (files := Z) d).send
                                         (fun w => (offlineSenders (files := Z) d).weights w.w₀)
                                         fun w => randK14 ((offlineSenders (files := Z) d).rand w.rc))).toRun.toTest.p :
        Block T12 Unit).rounds,
      ∀ o ∈ d'.opens, oldSrc 0 o.2 = true →
        o.2 ∈ (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).hand 2 ∧
          ((lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).tableAt o.2 k m).2.words = o.1.W := by
  intro w x k m
  obtain ⟨i1, i2, i3, i4⟩ := value_idx_numbers (Z := Z) hs scope
  obtain ⟨w1, w2, w3, w4⟩ := value_w_numbers (Z := Z) hs scope
  refine hwide_own K₀ d.source d.numbers d.later (keyAtValue (Z := Z) Z₀ d) (fillAtValue d Q x) ℓ Nm Mg₀
    _ rest Kp Vd _ w.1 w.2.1 x _ _ (S₁ w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x)
    (dValue d x) (dtValue d Q x) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x)
    (offlineSenders (files := Z) d).idx (offlineSenders (files := Z) d).w
    (offlineSenders (files := Z) d).send id _ hs scope ?_ ?_ ?_ k m
  · intro k v h
    exact idx_words hK₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).idx (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).own₀ i1 i2 i3
      i4 k v h
  · intro k v h
    exact w_words hK₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).w (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d).own₀ w1 w2 w3 w4
      k v h
  · intro k v h
    show (AtPublicFiles.KeyTreesKey.tbKey (AtPublicFiles.KeySharedThread.parKey d.source d.later) _ _ tk tt (.own 1) k v
      h).2.words = widthOmega
    rw [show AtPublicFiles.KeySharedThread.parKey d.source d.later = AtPublicFiles.AtFiles.Full.QK from
      AtPublicFiles.AtFiles.Full.par_sourced hs scope]
    exact omega_words hK₀ _ _ tk tt k v h

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.value_idx_numbers
#print axioms AtPublicFiles.OfflineRows.value_w_numbers
#print axioms AtPublicFiles.OfflineRows.last_wide
