-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinRunDoor.lean: THE JOIN's FIELD «run» (TheLots, E2E/OfflineJoin.lean) WITH NINE OF ITS TEN CLAUSES PAID: what a run
owes (AtRunS, E2E/KeyAcceptPairs.lean) at the offline prover's own senders and the written book, at every input that is
tied (TiedOffline, ok := inRange) and every coin, FROM ONE CLAUSE: DoorBehindS.

  LotDoorYes, lotDoorYes   clause (9): the door says yes (DoorYesS) at U₁ := Th …, U₂ := threadAt …, at their letters
  LotFinYes, lotFinYes     clause (10): the file's last test says yes (FinYesS) there, at every thread U₃ over the last
                           chain's own list of sub-protocols and every letter S₃
  runFromBehind            THE FIELD, from DoorBehindS at every R that ready returns

By what. doorYesS_key and finYesS_key (E2E/KeyLastDoor.lean), which hold at all letters of laid₁ and threadKey: Th
is laid₁ at the honest filling (T₁, E2E/FirstHFill.lean) and threadAt is threadKey (E2E/KeyStandWalked.lean): by unfolding.
The other seven clauses: runFromDoor (E2E/LotJoinRunStruck.lean).
Premises. Those of runFromDoor (live, hd, scope, fullPub = some K₀, hQ, hV, hPin) and hbs₃: U₃'s list is the last chain's.
[Inhabited Q₃] IS DATA, not a side condition: the frame's Tied reads «default» in its clause on the seam. The join lays
«Inhabited RunValue := ⟨fun _ => 0⟩»: a caller must lay the same term (E2E/LotJoinRunFits.lean does).
Limits. BOTH «YES» ARE IMPLICATIONS INSIDE: DoorYesS and FinYesS speak of states that stand at the chains' ENDS (ThrS at the
last border): that any run's state stands there is what the members' debts are for, and is not shown here; where none
stands, they hold idly. DoorBehindS stays owed. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotJoinRunStruck
import E2E.KeyLastDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open OnBytes (TableKey)
open AtPublicFiles.KeyLink (CoinOne AtRunS)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles TiedOffline relKeyZ)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue threadAt walkedLetter)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open ProofFile.Honest.Term (matrixInput tableCoins)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest
open ProofFile.Honest.K14 (WitLens)

/-- **Clause (9): the door says yes**, at the laid first thread and the shared thread, at their letters. -/
def LotDoorYes : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {P₁ Wt : Type}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true →
    ∀ (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) (ℓ : WitLens Wt) (Nm : NumbersS)
      (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
      (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
        Place × Table)
      (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
      (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
      (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
      (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : Xi) (k : Coins (keyBook K₀)),
      DoorYesS (keyFileDescription d.source d.numbers d.later)
        (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w₀ rc x)
        (threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd
          matrixReader (tableCoins Z) Z₀ w₀ rc x)
        (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w₀ rc x)
        (walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
          Vd matrixReader (tableCoins Z) Z₀ w₀ rc x) x k

theorem lotDoorYes : LotDoorYes := by
  intro Z d K₀ P₁ Wt live hd scope Q ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ w₀ rc x k
  exact AtPublicFiles.KeyLastChain.doorYesS_key _ w₀ rc x _ _ _ ℓ Nm Mg₀ _ rest Kp Vd _ _ _
    (AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok live hd) scope x k

/-- **Clause (10): the file's last test says yes**, at every thread over the last chain's list and every letter. -/
def LotFinYes : Prop :=
  ∀ {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {P₁ Wt : Type}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok d → InScope Z = true →
    ∀ (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) (ℓ : WitLens Wt) (Nm : NumbersS)
      (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
      (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
        Place × Table)
      (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
      (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
      (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
      (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : Xi) (k : Coins (keyBook K₀))
      (U₃ : Thread (keyBook K₀) (keyFileDescription d.source d.numbers d.later).S₃
        (keyFileDescription d.source d.numbers d.later).Cl (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit)
        (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
      (S₃ : Nat → Coins (keyBook K₀) → Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop),
      U₃.bs = (keyFileDescription d.source d.numbers d.later).second.blocksInOrder →
      FinYesS (keyFileDescription d.source d.numbers d.later)
        (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w₀ rc x)
        (threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd
          matrixReader (tableCoins Z) Z₀ w₀ rc x) U₃
        (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w₀ rc x)
        (walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
          Vd matrixReader (tableCoins Z) Z₀ w₀ rc x) S₃ x k

theorem lotFinYes : LotFinYes := by
  intro Z d K₀ P₁ Wt live hd scope Q ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ w₀ rc x k U₃ S₃ hbs₃
  exact AtPublicFiles.KeyLastChain.finYesS_key _ w₀ rc x _ _ _ ℓ Nm Mg₀ _ rest Kp Vd _ _ _ scope
    (AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok live hd).named U₃ hbs₃ S₃ x k

variable {Z : PublicFiles} {K₀ : KeyPub} {Q₂ Q₃ : Type} [Inhabited Q₃] {d : OfflineDescription}
  {Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness} (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray)
  {P₁ Wt : Type} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (U₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₃ (keyFileDescription d.source d.numbers d.later).Cl
    (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
  (S₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **THE FIELD run, from the one clause that is left: behind the door.** [Inhabited Q₃] is data: Tied's clause on the seam
reads its «default». -/
theorem runFromBehind (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hQ : Q.Rel = relKeyZ Z AtPublicFiles.AtFiles.inRange)
    (hV : ∀ w x, TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
      AtPublicFiles.AtFiles.inRange w x → Vd (inK w.1 w.2.1 x))
    (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hbs₃ : ∀ w x, (U₃ w x).bs = (keyFileDescription d.source d.numbers d.later).second.blocksInOrder)
    (behind : ∀ w x (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
        AtPublicFiles.AtFiles.inRange w x →
      ∀ R, ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
          (keyProver (offlineValue (files := Z) d)) w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R →
        DoorBehindS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
          (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
          (threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
            Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (U₃ w x)
          (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1
            w.2.1 x)
          (walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest
            Kp Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (S₃ w x) x
          ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R) :
    ∀ w x (c : CoinOne (keyBook K₀) Q₂ Q₃),
      TiedOffline Z d.source d.numbers d.later val₂ val₃ (offlineValue (files := Z) d)
        AtPublicFiles.AtFiles.inRange w x →
      AtRunS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
        (Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x)
        (threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp Vd
          matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (U₃ w x)
        (walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1
          x)
        (walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk tt rest Kp
          Vd matrixReader (tableCoins Z) Z₀ w.1 w.2.1 x) (S₃ w x) w x c :=
  runFromDoor val₂ val₃ ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ U₃ S₃ live hd scope hK hQ hV hPin
    fun w x c t => ⟨behind w x c t,
      lotDoorYes live hd scope Q ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ w.1 w.2.1 x _,
      lotFinYes live hd scope Q ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ w.1 w.2.1 x _ (U₃ w x) (S₃ w x)
        (hbs₃ w x)⟩

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.lotDoorYes
#print axioms AtPublicFiles.FirstH.Lots.lotFinYes
#print axioms AtPublicFiles.FirstH.Lots.runFromBehind
