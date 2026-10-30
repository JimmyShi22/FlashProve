-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinSharedAtValue.lean: THE JOIN's FOUR FIELDS ON THE TWO PROXIMITY TESTS AT A tt THAT IS A CLOSED TERM: `ttValue Z d K₀` (E2E/LotSharedAtValue.lean: texts over the
offline prover's own two jobs), so that no letter B is left: E2E/LotJoinSharedAtLots.lean's four at tt := ttValue.

  `eight_at`: in scope the linear claim's eight sub-protocols are made (`plan_key`, `Plan2.eight`).
  `ttAt_is_ttValue`: in scope ttF at the offline prover's senders IS ttValue, at every B (a reader's probe, taken over and
    proved here by JN_is_JKU, JO_is_JKO, bs_of).
  `valueThread`, `valueSaid`: the join's sharedThread, sharedSaid at the named letters and tt := ttValue; tk, rest, Z₀ stay letters.
  **`valueTestU`, `valueTestOmega`, `valueTestYesU`, `valueTestYesOmega`**: the four fields there.

Premises: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀.
Limits. Those of E2E/LotJoinSharedAtLots.lean: all content is ULaid.lean's trial and the called files'; ThrS inside every sentence.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinSharedAtLots
import E2E.LotSharedAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open ProofFile.Honest.K12.AtKey (keepsKey)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (PF QK par_sourced later_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeySharedThread (parKey plan_key)
open AtPublicFiles.KeyStandFull (idleNm idleMg)
open AtPublicFiles.KeyStandWalked.Lots (ttAt ttValue)
open AtPublicFiles.KeyDepthsAt (ttPlaced)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.HalvesAreJobs (JO bs_of)
open AtPublicFiles.TableFilled (JN_is_JKU JO_is_JKO)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) joinSharedAtValuePad : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) joinSharedAtValueRun : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) joinSharedAtValueRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- In scope the eight are made. -/
theorem eight_at {Z' : PublicFiles} (hs : KeySourced Z' d.source d.numbers d.later)
    (scope : InScope Z' = true) : Nonempty (Eight (parKey d.source PF)) := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  rw [later_sourced hs scope] at hQ
  exact hQ.eight

/-- **In scope ttF at the offline prover's senders is ttValue**, at every B. -/
theorem ttAt_is_ttValue {Z' : PublicFiles} (hs : KeySourced Z' d.source d.numbers d.later)
    (scope : InScope Z' = true) (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF)) :
    ttAt Z d K₀ Z₀ B = ttValue Z d K₀ := by
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  have e : parKey src PF = QK := par_sourced hs scope
  show ttPlaced K₀ (JN src _ B) (JO src _ B) () (ownTbl 1 (JO src _ B) () 43 fun _ _ _ => true) = _
  have hb := bs_of src (offlineSenders (files := Z) ⟨src, num, PF⟩) B rfl
  rw [JN_is_JKU src _ B e, JO_is_JKO src _ B e, ← hb]
  rfl

variable
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Words Cb.Gl.E)
  (Z₀ : ProofFile.Pub)

/-- The join's shared thread at the named letters, at a letter tt. -/
abbrev threadWith (tt : Nat → Coins (keyBook K₀) →
      Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  sharedThread WitLens.words idleNm (fun _ => idleMg) tk tt rest keepsKey (fun _ => True) Z₀ d w x

/-- Its letter. -/
abbrev saidWith (tt : Nat → Coins (keyBook K₀) →
      Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  sharedSaid WitLens.words idleNm (fun _ => idleMg) tk tt rest keepsKey (fun _ => True) Z₀ d w x

/-- At tt := ttValue. -/
abbrev valueThread := threadWith (d := d) tk rest Z₀ (ttValue Z d K₀)

abbrev valueSaid := saidWith (d := d) tk rest Z₀ (ttValue Z d K₀)

section
variable (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
  (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
include hd scope live hK₀

/-- **The ten sentences at a tied input, at ttValue.** -/
theorem ten_at_value (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : TiedAt Z d w x) (fall : ℕ → St → List Fmt.Drawn → Option String) :
    (PlaysS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 ∧
        BehindS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 ∧
        ExchangeS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 ∧
        RidesPastS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9) ∧
      (PlaysS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 ∧
        BehindS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 ∧
        ExchangeS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 ∧
        RidesPastS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10) ∧
      AcceptedS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) fall 9 ∧
      AcceptedS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) fall 10 := by
  have hs := sourced_of_ok live hd
  obtain ⟨B⟩ := eight_at hs scope
  have e : ttAt Z d K₀ Z₀ B = ttValue Z d K₀ := ttAt_is_ttValue hs scope Z₀ B
  have h := ten_at_tied tk rest Z₀ B hd scope live hK₀ w x ht fall
  have key : ∀ tt, ttAt Z d K₀ Z₀ B = tt →
      (PlaysS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 9 ∧
          BehindS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 9 ∧
          ExchangeS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 9 ∧
          RidesPastS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 9) ∧
        (PlaysS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 10 ∧
          BehindS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 10 ∧
          ExchangeS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) 10 ∧
          RidesPastS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x)
            10) ∧
        AcceptedS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) fall 9 ∧
        AcceptedS (threadWith (d := d) tk rest Z₀ tt w x) (saidWith (d := d) tk rest Z₀ tt w x) fall
          10 := by
    intro tt htt
    subst htt
    exact h
  exact key _ e

/-- **The field testU, at ttValue.** -/
theorem valueTestU : ∀ w x, TiedAt Z d w x →
    PlaysS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 ∧
      BehindS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 ∧
      ExchangeS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 ∧
      RidesPastS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 9 :=
  fun w x ht => (ten_at_value tk rest Z₀ hd scope live hK₀ w x ht fun _ _ _ => none).1

/-- **The field testOmega, at ttValue.** -/
theorem valueTestOmega : ∀ w x, TiedAt Z d w x →
    PlaysS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 ∧
      BehindS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 ∧
      ExchangeS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 ∧
      RidesPastS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x) 10 :=
  fun w x ht => (ten_at_value tk rest Z₀ hd scope live hK₀ w x ht fun _ _ _ => none).2.1

/-- **The field testYesU, at ttValue.** -/
theorem valueTestYesU : ∀ w x, TiedAt Z d w x →
    AcceptedS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x)
      (fallsBy [] (descOf d).shared.blocksInOrder) 9 :=
  fun w x ht => (ten_at_value tk rest Z₀ hd scope live hK₀ w x ht _).2.2.1

/-- **The field testYesOmega, at ttValue.** -/
theorem valueTestYesOmega : ∀ w x, TiedAt Z d w x →
    AcceptedS (valueThread (d := d) tk rest Z₀ w x) (valueSaid (d := d) tk rest Z₀ w x)
      (fallsBy [] (descOf d).shared.blocksInOrder) 10 :=
  fun w x ht => (ten_at_value tk rest Z₀ hd scope live hK₀ w x ht _).2.2.2

end

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.eight_at
#print axioms AtPublicFiles.AtFiles.HonestTerm.ttAt_is_ttValue
#print axioms AtPublicFiles.AtFiles.HonestTerm.ten_at_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.valueTestU
#print axioms AtPublicFiles.AtFiles.HonestTerm.valueTestOmega
#print axioms AtPublicFiles.AtFiles.HonestTerm.valueTestYesU
#print axioms AtPublicFiles.AtFiles.HonestTerm.valueTestYesOmega
