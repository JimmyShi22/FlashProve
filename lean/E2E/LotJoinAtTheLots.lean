-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinAtTheLots.lean: THE LAST CALL OF THE LAYING: TheLots (E2E/OfflineJoin.lean) from its twin LotsAt (E2E/LotJoinLaid.lean), field
by field; and so the join's last line from what is left.

  `theLots_of_lotsAt`: TheLots at any U₁, U₃, S₁, S₃ from LotsAt at Tied := TiedAt Z description, the join's own prover of the bare
    sides, U₂ := sharedThread …, S₂ := sharedSaid …, and the join's two types of run values.
  `rel_of_tiedAt`: a tied input meets the laid relation: the frame's Tied.rel: (laterValue Z d K₀).Rel is relKeyZ Z inRange by its text.
  `theLots_of_left`: TheLots at the laid first chain from LeftLots.
  **`keyAccepts_of_left`**: THE END: KeyAccepts of the offline prover, at the empty fall, at the served requests, at the letters that the join's holder
    has named (ℓ := WitLens.words, Nm := idleNm, Mg₀ := idleMg, Kp := keepsKey, Vd := True: keyAccepts_at_value, E2E/OfflineJoinLaws.lean), FROM ONE STRUCTURE OF
    WHAT IS LEFT. tk, tt, rest, Z₀ and the last chain's U₃, S₃ stay letters.
  `LeftEnd`: THE FINEST STRUCTURE OF RECORD, TEN FIELDS, NONE OF THE FIRST CHAIN: behind (ONE of AtRunS's ten clauses: DoorBehindS, at every R that ready returns:
    runFromBehind, E2E/LotJoinRunDoor.lean) · lastList (U₃'s list of sub-protocols is the last chain's) · and the eight fields that no lot of ours touches: sits, lastOwes, lastNext, lastYes, testU, testOmega,
    testYesU, testYesOmega.
  **`keyAccepts_of_end`**: KeyAccepts from it.

Typed against E2E/OfflineJoin.lean. If a field there turns, this file goes red at that field: that is
what it is for.

★ WHAT THE NAMED LETTERS ARE WORTH. Nm := idleNm, Mg₀ := idleMg, Vd := True are called idle, BUT THE SHARED THREAD DOES NOT READ Mg₀ BARE: its meaning is mgWords … (Mg₀ w)
(Johnson/Desc/ProofFile/Honest/K14/Thread2.lean), which lays the kind's own sentences over pin, nearU, recRow, omU and row (SmpOwn, NearAt, RecAll, OmU, RowsU, FoldAt, RowsO); of Mg₀ it
keeps pinT and the five fields of own items, and an own item is True in the shared thread by that thread's own text. So at these letters every item that members 9 and 10 shut
or owe IS A REAL SENTENCE (by a probe that is not in this tree: each by rfl); what is idle is pinT (open at borders 0 and 1) and Vd.
WHETHER THE FIELDS OF WHAT IS LEFT ARE MET AT THESE LETTERS IS OPEN: nothing here shows a member; if there is none, the end is true and empty.

WHICH LETTERS STAY. In theLots_of_lotsAt and theLots_of_left all of ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀, U₃, S₃. In the two ends (keyAccepts_of_left, keyAccepts_of_end) FIVE ARE LAID (ℓ, Nm, Mg₀, Kp,
Vd); tk', tt', rest', Z₀, U₃, S₃ stay. tt' IS NOT FREE IN TRUTH: PlaysS at 9 and 10 says that the halves' new trees show what the thread's tables name, so testU and testOmega can hold only where tt' is the
halves' own tables (ttValue, E2E/LotSharedAtValue.lean): at a wrong tt' LeftEnd has no member.
WHERE THE FILE STANDS. By what it imports (the lookups' law at 4, 10) the join's end now stands above the side library AtFullSide/.

Limits. Those of E2E/LotJoinLaid.lean and E2E/OfflineJoin.lean. AN IMPLICATION. leftEnd_of_last (E2E/LotJoinEnd.lean) gives a member of LeftEnd from LeftLast; no member of LeftLots is known. Nothing on soundness, completeness, hiding or
binding.
-/
import E2E.OfflineJoin
import E2E.OfflineJoinLaws
import E2E.LotJoinLaid
import E2E.LotJoinRunStruck
import E2E.LotJoinRunDoor

set_option autoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Thread Local Common Coins Mid Table)
open ProofFile.Honest.K14 (WitLens)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open AtPublicFiles.FirstH.Lots (LotsAt LeftLots lotsFromLeft laidFirst laidSaid laterValue)

local instance (priority := high) padsNonemptyAtTheLots : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) runValueNonemptyAtTheLots : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) runValueInhabitedAtTheLots : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}
  {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub)

/-- **TheLots from its twin**, field by field. -/
theorem theLots_of_lotsAt {U₁ : FirstFamily Z description (keyBook K₀)}
    {U₃ : LastFamily Z description (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (L : LotsAt (d := description) (K₀ := K₀) (TiedAt Z description)
      ((bareSides (descOf description) (keyBook K₀) (proverOf Z description) [] [] []).prover
        (proverOf Z description))
      U₁ (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description) U₃ S₁
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description) S₃ RunValue RunValue) :
    TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description U₁ U₃ S₁ S₃ where
  sits := L.sits
  firstOwes := L.firstOwes
  lastOwes := L.lastOwes
  firstNext := L.firstNext
  lastNext := L.lastNext
  firstYes := L.firstYes
  lastYes := L.lastYes
  testU := L.testU
  testOmega := L.testOmega
  testYesU := L.testYesU
  testYesOmega := L.testYesOmega
  run := L.run

/-- A tied input meets the laid relation. -/
theorem rel_of_tiedAt (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)
    (ht : TiedAt Z description w x) : (laterValue Z description K₀).Rel w.1 w.2.1 x := by
  exact ht.rel

/-- **TheLots at the laid first chain, from what is left.** -/
theorem theLots_of_left {U₃ : LastFamily Z description (keyBook K₀)}
    {S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok description)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (left : LeftLots (d := description) (K₀ := K₀) (TiedAt Z description)
      ((bareSides (descOf description) (keyBook K₀) (proverOf Z description) [] [] []).prover
        (proverOf Z description))
      (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description) U₃
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description) S₃ RunValue RunValue) :
    TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description (laidFirst Z description K₀) U₃
      (laidSaid Z description K₀) S₃ :=
  theLots_of_lotsAt ℓ Nm Mg₀ tk tt rest Kp Vd Z₀
    (lotsFromLeft hd scope live hK₀ (fun w x ht => rel_of_tiedAt w x ht) left)

/-- **THE END: KeyAccepts FROM WHAT IS LEFT**, at the named letters of the shared chain. -/
theorem keyAccepts_of_left
    (tk' : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Place × Table)
    (tt' : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Place × Table)
    (rest' : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → OnBytes.Means.Words Cb.Gl.E)
    {U₃ : LastFamily Z description (keyBook K₀)} {S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok description) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (left : LeftLots (d := description) (K₀ := K₀) (TiedAt Z description)
      ((bareSides (descOf description) (keyBook K₀) (proverOf Z description) [] [] []).prover
        (proverOf Z description))
      (sharedThread ProofFile.Honest.K14.WitLens.words AtPublicFiles.KeyStandFull.idleNm
        (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest' ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀
        description) U₃
      (sharedSaid ProofFile.Honest.K14.WitLens.words AtPublicFiles.KeyStandFull.idleNm
        (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest' ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀
        description) S₃ RunValue RunValue) :
    AtPublicFiles.Bridge.KeyAccepts (offlineProverWithEncodedTable Z (descOf description) (thePartsAt Z).book
                  ((thePartsAt Z).prover description) runValueBytes runValueBytes (offlineStart description))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_at_value hr tk' tt' rest' Z₀ hd scope live hK₀
    (theLots_of_left ProofFile.Honest.K14.WitLens.words AtPublicFiles.KeyStandFull.idleNm
      (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest' ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀ hd
      scope live hK₀ left)

section End
variable
    (tk' : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Place × Table)
    (tt' : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → Place × Table)
    (rest' : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
      List Fmt.Drawn → OnBytes.Means.Words Cb.Gl.E)

/-- The join's shared thread at the named letters. -/
abbrev namedShared (description : OfflineDescription) :=
  sharedThread (Z := Z) ProofFile.Honest.K14.WitLens.words AtPublicFiles.KeyStandFull.idleNm
    (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest' ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀
    description

/-- Its letter. -/
abbrev namedSharedSaid (description : OfflineDescription) :=
  sharedSaid (Z := Z) ProofFile.Honest.K14.WitLens.words AtPublicFiles.KeyStandFull.idleNm
    (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest' ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀
    description

/-- **WHAT IS LEFT, AT ITS FINEST.** A premise's form. leftEnd_of_last (E2E/LotJoinEnd.lean) gives a member from LeftLast. -/
structure LeftEnd (description : OfflineDescription) (U₃ : LastFamily Z description (keyBook K₀))
    (S₃ : OwnLetter Z (keyBook K₀)) : Prop where
  /-- a run: behind the door -/
  behind : ∀ w x (c : CoinOne (keyBook K₀) RunValue RunValue), TiedAt Z description w x →
    ∀ R, ProofFile.Honest.ready (descOf description) (keyBook K₀) (proverOf Z description) w.1 w.2.1 x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
      ProofFile.Honest.DoorBehindS (descOf description) (proverOf Z description)
        (laidFirst Z description K₀ w x) (namedShared Z₀ tk' tt' rest' description w x) (U₃ w x)
        (laidSaid Z description K₀ w x) (namedSharedSaid Z₀ tk' tt' rest' description w x) (S₃ w x) x
        ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R
  /-- the last thread's list is the last chain's -/
  lastList : ∀ w x, (U₃ w x).bs = (descOf description).second.blocksInOrder
  sits : ∀ w x, TiedAt Z description w x → (descOf description).okStart x = true →
    ProofFile.Honest.Sits (descOf description)
      ((bareSides (descOf description) (keyBook K₀) (proverOf Z description) [] [] []).prover
        (proverOf Z description))
      (laidFirst Z description K₀ w x) (namedShared Z₀ tk' tt' rest' description w x) (U₃ w x)
  lastOwes : ∀ w x, TiedAt Z description w x → ProofFile.Honest.OwesS (U₃ w x) (S₃ w x)
  lastNext : ∀ w x, TiedAt Z description w x → ∀ b, ProofFile.Honest.SaidNext (U₃ w x) (S₃ w x) b
  lastYes : ∀ w x, TiedAt Z description w x →
    ProofFile.Honest.YesS (U₃ w x) (S₃ w x) (ProofFile.Honest.fallsBy [] (descOf description).second.blocksInOrder)
  testU : ∀ w x, TiedAt Z description w x →
    ProofFile.Honest.PlaysS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 9 ∧
      ProofFile.Honest.BehindS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 9 ∧
      ProofFile.Honest.ExchangeS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 9 ∧
      ProofFile.Honest.RidesPastS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 9
  testOmega : ∀ w x, TiedAt Z description w x →
    ProofFile.Honest.PlaysS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 10 ∧
      ProofFile.Honest.BehindS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 10 ∧
      ProofFile.Honest.ExchangeS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 10 ∧
      ProofFile.Honest.RidesPastS (namedShared Z₀ tk' tt' rest' description w x)
        (namedSharedSaid Z₀ tk' tt' rest' description w x) 10
  testYesU : ∀ w x, TiedAt Z description w x →
    ProofFile.Honest.AcceptedS (namedShared Z₀ tk' tt' rest' description w x)
      (namedSharedSaid Z₀ tk' tt' rest' description w x)
      (ProofFile.Honest.fallsBy [] (descOf description).shared.blocksInOrder) 9
  testYesOmega : ∀ w x, TiedAt Z description w x →
    ProofFile.Honest.AcceptedS (namedShared Z₀ tk' tt' rest' description w x)
      (namedSharedSaid Z₀ tk' tt' rest' description w x)
      (ProofFile.Honest.fallsBy [] (descOf description).shared.blocksInOrder) 10

/-- **TheLots at the named letters and the laid first chain, from what is left at its finest.** -/
theorem theLots_of_end {U₃ : LastFamily Z description (keyBook K₀)} {S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok description) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (left : LeftEnd Z₀ tk' tt' rest' description U₃ S₃) :
    TheLots (Z := Z) ProofFile.Honest.K14.WitLens.words AtPublicFiles.KeyStandFull.idleNm
      (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest' ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀
      description (laidFirst Z description K₀) U₃ (laidSaid Z description K₀) S₃ where
  sits := left.sits
  firstOwes := AtPublicFiles.FirstH.Lots.joinFirstOwes (TiedAt Z description) hd scope live rfl fun w x _ =>
    AtPublicFiles.FirstH.Lots.leftJoin_laid (AtPublicFiles.FirstH.Lots.sourced_of_description hd live) scope hK₀ w x
  lastOwes := left.lastOwes
  firstNext := AtPublicFiles.FirstH.Lots.joinFirstNext (TiedAt Z description)
  lastNext := left.lastNext
  firstYes := AtPublicFiles.FirstH.Lots.joinFirstYes (TiedAt Z description) hd scope live rfl fun w x _ =>
    AtPublicFiles.FirstH.Lots.leftJoin_laid (AtPublicFiles.FirstH.Lots.sourced_of_description hd live) scope hK₀ w x
  lastYes := left.lastYes
  testU := left.testU
  testOmega := left.testOmega
  testYesU := left.testYesU
  testYesOmega := left.testYesOmega
  run := AtPublicFiles.FirstH.Lots.runFromBehind runValueBytes runValueBytes ProofFile.Honest.K14.WitLens.words
    AtPublicFiles.KeyStandFull.idleNm (fun _ => AtPublicFiles.KeyStandFull.idleMg) tk' tt' rest'
    ProofFile.Honest.K12.AtKey.keepsKey (fun _ => True) Z₀ U₃ S₃ live hd scope hK₀ rfl
    (fun _ _ _ => trivial) (fun _ => idle_pin) left.lastList left.behind

/-- **THE END, AT ITS FINEST: KeyAccepts FROM «BEHIND THE DOOR» AND THE EIGHT UNTOUCHED FIELDS.** -/
theorem keyAccepts_of_end {U₃ : LastFamily Z description (keyBook K₀)} {S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok description) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (left : LeftEnd Z₀ tk' tt' rest' description U₃ S₃) :
    AtPublicFiles.Bridge.KeyAccepts (offlineProverWithEncodedTable Z (descOf description) (thePartsAt Z).book
                  ((thePartsAt Z).prover description) runValueBytes runValueBytes (offlineStart description))
      (lettersZ Z allZeroDigest []).W (fun _ _ _ => ∅) (fun _ _ => ∅) (ServedRequest committerCoinCountLessOne Z hr) :=
  keyAccepts_at_value hr tk' tt' rest' Z₀ hd scope live hK₀
    (theLots_of_end Z₀ tk' tt' rest' hd scope live hK₀ left)

end End

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.theLots_of_end
#print axioms AtPublicFiles.AtFiles.HonestTerm.keyAccepts_of_end
#print axioms AtPublicFiles.AtFiles.HonestTerm.keyAccepts_of_left
#print axioms AtPublicFiles.AtFiles.HonestTerm.theLots_of_lotsAt
#print axioms AtPublicFiles.AtFiles.HonestTerm.rel_of_tiedAt
#print axioms AtPublicFiles.AtFiles.HonestTerm.theLots_of_left
