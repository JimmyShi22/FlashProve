-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLastFields.lean: THE THREE FIELDS `lastOwes`, `lastNext`, `lastYes` OF `TheLots` (E2E/OfflineJoin.lean), to the letter, at the last
chain's thread and letter as terms (`lastThread`, `lastSaid`, E2E/OfflineLastTerms.lean): by one call of `last_laid`
(E2E/KeyLastLaid.lean), from what that law still asks at these letters, under five names.

  `lastJobAt d`   the job of the last chain's proximity test at the offline prover's own senders
  `LastLeft`      WHAT STAYS: five named premises, each in `last_laid`'s own words at `lastThread`'s letters:
                  fit (the key fits the shape's index at the shared thread's valid inputs) · sent (three public equations on
                  what the three sendings send) · tie (at every stand at the border 2, the thread's words are the job's
                  plain rows) · hold (there the three trees that the test takes over are at hand) · wide (their widths)
  `last_fields`   the three fields from `LastLeft`

Paid here, by name: hd `d_lin`, hdM `dM_opened`, hsame `same_value`, ho₀ `orc_zero`, hDt `dot_value`, hown `own_value`
(E2E/OfflineLastTerms.lean) · ho₂ `orc_two` (E2E/KeyLastNumbers.lean) · hrow `second_laid_keyOf` (E2E/OfflineLastLaid.lean).

All the join's letters ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀, the filling's letter Q and the first chain's letter S₁ are free.

Limits. CONDITIONAL on `LastLeft`: no member is shown here. `OwesS` and `YesS` speak of every stand of the thread: that the thread
stands at any border is not said here. Nothing on any property.
-/
import E2E.OfflineLastTerms
import E2E.OfflineLastLaid
import E2E.KeyLastLaid
import E2E.KeyLastNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (jobOmega WitLens)
open ProofFile.Honest.K12.Light (ManyJob plainMany askOf)
open ProofFile.Honest.Term (tableCoins)
open OnBytes (TableKey)
open OnBytes.Means (Words tableSize layoutOf)
open OnBytes.Slice (begun frS)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (randK14)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyLay (jobKWAt parIK parWK shapeOK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLastChain (last_laid orc_two wordsKey val₁Key)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed (PadZ pads_nonempty)
open VerifierAndGoals (PublicFiles InScope)

local instance (priority := high) lastFieldsPads : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) lastFieldsRunValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) lastFieldsRunValueInhabited : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles}

/-- **The job of the last chain's proximity test, at the offline prover's own senders.** -/
abbrev lastJobAt (d : OfflineDescription) : ManyJob (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit :=
  jobKWAt d.source d.numbers d.later (offlineSenders (files := Z) d).idx
    (offlineSenders (files := Z) d).w (offlineSenders (files := Z) d).send id
    (askOf (offlineSenders (files := Z) d).send
      (fun w => (offlineSenders (files := Z) d).weights w.w₀)
      fun w => randK14 ((offlineSenders (files := Z) d).rand w.rc))

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

/-- **WHAT STAYS of `last_laid`'s premises at `lastThread`'s letters.** NAMED PREMISES: no member is shown here. -/
structure LastLeft : Prop where
  /-- the key fits the shape's index, at the shared thread's valid inputs -/
  fit : ∀ w x, TiedAt Z d w x → ∀ v,
    (threadKey d.source d.numbers d.later (keyAtValue (Z := Z) Z₀ d) ℓ Nm Mg₀
      (AtPublicFiles.KeyAsksKey.tableKey d.source d.later K₀ (keyAtValue (Z := Z) Z₀ d) tk tt) rest Kp Vd
      (AtPublicFiles.KeyStandOne.inK w.1 w.2.1 x)).valid v → keyFits v.key QK.par.S.fold.index = true
  /-- what the index masks' sending sends -/
  sentIndexMasks : (offlineSenders (files := Z) d).idx.P.sent = parIK.sent
  /-- what W's sending sends -/
  sentW : (offlineSenders (files := Z) d).w.P.sent = parWK.sent
  /-- the shape of what Omega's sending sends first -/
  shapeOmega : ∀ n, ((jobOmega ⟨(offlineSenders (files := Z) d).send.P,
    n + (offlineSenders (files := Z) d).send.atPoint⟩).Q.sent.getD 0 default).shape = shapeOK
  /-- at every stand at the border 2 the thread's words are the job's plain rows -/
  tie : ∀ w x, TiedAt Z d w x → ∀ k st m E
      (c : RowCoins [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest]),
    ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2 k st m E →
    lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (lastJobAt (Z := Z) d).toRun.toTest.p.place
      [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest] 0 = .ok c →
    ∀ G, st.st.groups[st.loc.own]? = some G → ∀ o ∈ G.members.toList, ∀ pt,
      ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key d.source (fillAtValue d Q x)) st
            ((lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).wit k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany (lastJobAt (Z := Z) d) m.st.input (frontOf m)
              (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1)) o pt i
  /-- there the three trees that the test takes over are at hand -/
  hold : ∀ w x, TiedAt Z d w x → ∀ k st m E
      (c : RowCoins [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest]),
    ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2 k st m E →
    lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (lastJobAt (Z := Z) d).toRun.toTest.p.place
      [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest] 0 = .ok c →
    OldAt E ((lastJobAt (Z := Z) d).toRun.toTest.trees₀ m.st.input (frontOf m)
        (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1).mem
        ((lastJobAt (Z := Z) d).toRun.toTest.first m.st.input (frontOf m)
          (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1)))
      (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0))
  /-- their widths -/
  wide : ∀ w x (k : Coins (keyBook K₀)) (m : Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
    ∀ d' ∈ (proximityTestKind guardedProximityTestParts (lastJobAt (Z := Z) d).toRun.toTest.p : Block T12 Unit).rounds,
      ∀ o ∈ d'.opens, oldSrc 0 o.2 = true →
        o.2 ∈ (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).hand 2 ∧ ((lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x).tableAt o.2 k m).2.words = o.1.W

variable {ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁}

/-- **The three fields of `TheLots` at the last chain, from what stays.** -/
theorem last_fields (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) (left : LastLeft ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁) :
    (∀ w x, TiedAt Z d w x → OwesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)) ∧
      (∀ w x, TiedAt Z d w x → ∀ b, SaidNext (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) b) ∧
      ∀ w x, TiedAt Z d w x →
        YesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (fallsBy [] (descOf d).second.blocksInOrder) := by
  have main : ∀ w x, TiedAt Z d w x →
      OwesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) ∧
        (∀ b, SaidNext (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) b) ∧
        YesS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) (fallsBy [] (descOf d).second.blocksInOrder) := fun w x ht =>
    last_laid K₀ d.source d.numbers d.later (keyAtValue (Z := Z) Z₀ d) (fillAtValue d Q x) ℓ Nm Mg₀ _ rest
      Kp Vd _ w.1 w.2.1 x _ _ (S₁ w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (dValue d x)
      (dtValue d Q x) 6 11 (fun _ => True) ⟨w.1, w.2.1, x, ()⟩ dTValue (dMValue w x)
      (offlineSenders (files := Z) d).idx (offlineSenders (files := Z) d).w
      (offlineSenders (files := Z) d).send id _ hs scope hK₀ (left.fit w x ht) (d_lin d x)
      (dM_opened w x) left.sentIndexMasks left.sentW left.shapeOmega (same_value d Q x) (orc_zero d)
      (orc_two hs scope) (dot_value d Q x) (left.tie w x ht) (left.hold w x ht) (left.wide w x)
      (own_value Z₀ d) (second_laid_keyOf _ _ _ _ _ _ _ _ _ _ _ hs scope hK₀ _ _ _) _
  exact ⟨fun w x ht => (main w x ht).1, fun w x ht => (main w x ht).2.1, fun w x ht => (main w x ht).2.2⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.last_fields
