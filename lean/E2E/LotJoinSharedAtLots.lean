-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinSharedAtLots.lean: THE JOIN's FOUR FIELDS ON THE SHARED CHAIN's TWO PROXIMITY TESTS: testU, testOmega, testYesU, testYesOmega of `TheLots`
(E2E/OfflineJoin.lean), IN THAT STRUCTURE's OWN WORDS, AT THE LETTERS AT WHICH E2E/OfflineJoinLaws.lean pays the laws on letters: ℓ := WitLens.words,
Nm := idleNm, Mg₀ := fun _ => idleMg, Kp := keepsKey, Vd := fun _ => True; tt := `ttAt Z d K₀ Z₀ B` (E2E/LotJoinShared.lean); tk, rest, Z₀ stay letters.

  `key_of_tied`: a tied input's instance is the committer's sample at some seed (`validAt_of_tied`, as `shared_at_tied` spends it).
  `ten_at_tied`: the ten sentences at a tied input, at every fall.
  **`joinTestU`, `joinTestOmega`, `joinTestYesU`, `joinTestYesOmega`**: the four fields: each is one call.

OVER WHICH TEXTS IT RIDES: E2E/OfflineJoinLaws.lean · E2E/KeyStandFull.lean,
as they stand in this tree.

Premises: offlineDescription Z = .ok d · InScope Z · protocolDataWellFormed (asDescriptionFiles Z) · fullPub = some K₀. B : Eight (parKey d.source PF) is a letter: in scope there is
one (`plan_key`, `Plan2.eight`); the join's ends do not name tt, so whoever calls them may take any.

Limits. ALL CONTENT IS IN Johnson/Desc/ProofFile/Honest/K12/AtKey/ULaid.lean (of the grade «trial» by its own letter) and in the called files; here: ties and calls.
WHAT THE ITEMS SAY AT THESE LETTERS: the thread does not read Mg₀ bare: it reads `mgWords` … (Mg₀ w) (Johnson/Desc/ProofFile/Honest/K14/Thread2.lean), which lays the kind's own
sentences (SmpOwn, NearAt, RecAll, OmU, RowsU, FoldAt, RowsO) over the fields pin, nearU, recRow, omU, row. Of idleMg it keeps the stored table's pin (pinT) and the
own items' fields: these say True. So the items that members 9 and 10 shut or owe are these sentences. Read at that file; not shown here.
Every sentence has ThrS as a premise inside. At the written sizes. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinShared
import E2E.OfflineJoinLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12.AtKey (keepsKey)
open ProofFile.Honest.Term (tableCoins)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyOodTie (validAt_of_tied)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleNm_tenant)
open AtPublicFiles.KeyStandWalked.Lots (ttAt lotJoinShared)
open Bind.ForProver (shapeOf oodSh Seed)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) joinSharedAtLotsPad : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) joinSharedAtLotsRun : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) joinSharedAtLotsRunDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}

/-- **A tied input's instance is the committer's sample at some seed.** -/
theorem key_of_tied (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (Z₀ : ProofFile.Pub)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : TiedAt Z d w x) :
    ∃ sd : Seed (shapeOf (pubKey Z₀ d.source.chains)) × ℕ,
      x = ⟨oodSh (shapeOf (pubKey Z₀ d.source.chains)) (pubKey Z₀ d.source.chains)
        ⟨matrixReader w.1, tableCoins Z w.2.1, sd⟩⟩ := by
  have sourced := sourced_of_ok live hd
  have hk := AtPublicFiles.AtFiles.sized_sourced sourced scope
  obtain ⟨sd, hsd⟩ := validAt_of_tied Z rfl ht Z₀ d.source.chains hk
  refine ⟨sd, ?_⟩
  cases x with
  | mk key => exact congrArg Xi.mk hsd

variable
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Words Cb.Gl.E)
  (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF))

/-- The join's shared thread at the named letters. -/
abbrev namedThread (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  sharedThread WitLens.words idleNm (fun _ => idleMg) tk (ttAt Z d K₀ Z₀ B) rest keepsKey (fun _ => True)
    Z₀ d w x

/-- Its letter. -/
abbrev namedSaid (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  sharedSaid WitLens.words idleNm (fun _ => idleMg) tk (ttAt Z d K₀ Z₀ B) rest keepsKey (fun _ => True)
    Z₀ d w x

section
variable (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
  (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
include hd scope live hK₀

/-- **The ten sentences at a tied input.** -/
theorem ten_at_tied (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : TiedAt Z d w x) (fall : ℕ → St → List Fmt.Drawn → Option String) :
    (PlaysS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 ∧
        BehindS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 ∧
        ExchangeS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 ∧
        RidesPastS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9) ∧
      (PlaysS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 ∧
        BehindS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 ∧
        ExchangeS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 ∧
        RidesPastS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10) ∧
      AcceptedS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) fall 9 ∧
      AcceptedS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) fall 10 := by
  obtain ⟨sd, hx⟩ := key_of_tied hd scope live Z₀ w x ht
  exact lotJoinShared Z d K₀ WitLens.words idleNm (fun _ => idleMg) tk rest (fun _ => True) Z₀ B w.1 w.2.1
    x (sourced_of_ok live hd) scope hK₀ sd hx idleNm_tenant (fun _ => idle_cells) trivial fall

/-- **The field testU.** -/
theorem joinTestU : ∀ w x, TiedAt Z d w x →
    PlaysS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 ∧
      BehindS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 ∧
      ExchangeS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 ∧
      RidesPastS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 9 :=
  fun w x ht => (ten_at_tied tk rest Z₀ B hd scope live hK₀ w x ht fun _ _ _ => none).1

/-- **The field testOmega.** -/
theorem joinTestOmega : ∀ w x, TiedAt Z d w x →
    PlaysS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 ∧
      BehindS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 ∧
      ExchangeS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 ∧
      RidesPastS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x) 10 :=
  fun w x ht => (ten_at_tied tk rest Z₀ B hd scope live hK₀ w x ht fun _ _ _ => none).2.1

/-- **The field testYesU.** -/
theorem joinTestYesU : ∀ w x, TiedAt Z d w x →
    AcceptedS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x)
      (fallsBy [] (descOf d).shared.blocksInOrder) 9 :=
  fun w x ht => (ten_at_tied tk rest Z₀ B hd scope live hK₀ w x ht _).2.2.1

/-- **The field testYesOmega.** -/
theorem joinTestYesOmega : ∀ w x, TiedAt Z d w x →
    AcceptedS (namedThread tk rest Z₀ B w x) (namedSaid tk rest Z₀ B w x)
      (fallsBy [] (descOf d).shared.blocksInOrder) 10 :=
  fun w x ht => (ten_at_tied tk rest Z₀ B hd scope live hK₀ w x ht _).2.2.2

/-- A TEST OF THE WORDS, no payment: the four drop into `TheLots` at these letters as its fields. -/
example {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (L₀ : TheLots (Z := Z) WitLens.words idleNm (fun _ => idleMg) tk (ttAt Z d K₀ Z₀ B) rest keepsKey
      (fun _ => True) Z₀ d U₁ U₃ S₁ S₃) :
    TheLots (Z := Z) WitLens.words idleNm (fun _ => idleMg) tk (ttAt Z d K₀ Z₀ B) rest keepsKey
      (fun _ => True) Z₀ d U₁ U₃ S₁ S₃ :=
  { L₀ with
    testU := joinTestU tk rest Z₀ B hd scope live hK₀
    testOmega := joinTestOmega tk rest Z₀ B hd scope live hK₀
    testYesU := joinTestYesU tk rest Z₀ B hd scope live hK₀
    testYesOmega := joinTestYesOmega tk rest Z₀ B hd scope live hK₀ }

end

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.key_of_tied
#print axioms AtPublicFiles.AtFiles.HonestTerm.ten_at_tied
#print axioms AtPublicFiles.AtFiles.HonestTerm.joinTestU
#print axioms AtPublicFiles.AtFiles.HonestTerm.joinTestOmega
#print axioms AtPublicFiles.AtFiles.HonestTerm.joinTestYesU
#print axioms AtPublicFiles.AtFiles.HonestTerm.joinTestYesOmega
