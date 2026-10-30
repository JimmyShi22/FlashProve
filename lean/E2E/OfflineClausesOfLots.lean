-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineClausesOfLots.lean: HOW THE OFFLINE HALF OF ZERO KNOWLEDGE HANGS ON THE OFFLINE HALF OF COMPLETENESS. The three offline lines
of zero knowledge at the protocol's offline honest prover, `offlineProver (thePartsAt files)`, FROM WHAT IS SPENT OF THE OFFLINE
PROVER's DEBTS ON ACCEPTANCE, at one set of letters. NO PREMISE OF TRUTH IS LEFT: at each of the four proximity tests the
sentence that the rows taken in say true is paid from the thread's own stand.

  `fourOwed_of_spent`            `FourOwed d` (E2E/OfflineClausesOfFourOwed.lean): owed at the four tests' rows
  `offline_clauses_of_spent`     the three lines, from `LotsSpent` (E2E/OfflineLotsSpent.lean: no field of it says yes)
  `offline_rows_three_of_spent`  the three that are asked of the rows: `IsProvK`, `Owed` at the muted rows, every owner has a row
  `offline_clauses_of_lots`      the three lines, from `TheLots` (E2E/OfflineJoin.lean); of its join's five side premises the three on the
                               keeping are paid at `keepsKey` (`keepsKey_same`, `keepsKey_zero`, `keepsKey_eleven`); two stay, on the letters Nm, Mg₀

THE ONE SET OF LETTERS. The first chain's thread: `firstFamilyAt d Q` · the shared chain's filled table and keeping: `ttLaid Z d K₀ Z₀ B`,
`keepsKey` · the last chain's thread and letter: `lastThread`, `lastSaid` at the same letters. Free: ℓ, Nm (its tenant one to one), Mg₀,
tk, rest, Vd, Z₀, B, Q, S₁.

THE FOUR ROWS. Ranges: `rangesTestOwed_of_lots` (E2E/OfflineClausesAtTheTerm.lean) · folded row's group, Omega's group:
`testOnFoldedRowOwed_of_lots`, `testOnOmegaOwed_of_lots` (E2E/OfflineSharedTestsOwedOfLots.lean) · own group: `ownOwed_of_spent`
(E2E/OfflineOwnOwedOfLots.lean).

ON THE COINS. The condition at a test's second part (On) reads the input and the carried coins. It is OWED: each of the four fields is
shown at every input in the key file's relation, AT EVERY COIN of the book and every due list of challenges, at the run's own
stand; `exact` is claimed under it. Nowhere is it a hypothesis on a run under which coins are then sampled anew, and no law
here conditions the coins on it. The lemma that gives the stand at every coin, in all four rows: `threads_at_spent`
(E2E/OfflineLotsSpent.lean): one seed, the relation's own, then every coin. The relation takes in every index in range, every
table randomness and every seed (E2E/OfflineRelationIsWhole.lean).

Limits. CONDITIONAL on `LotsSpent` (or `TheLots`) at these letters: no member of either is given here: SO NO ZERO KNOWLEDGE OF ANY PROTOCOL
IS PROVED HERE. The limits of the sixteen rows' files stand. The state on entry of each test is the job's own. In scope, where the
public files' test says yes, at the written book.
-/
import E2E.OfflineClausesAtTheTerm
import E2E.OfflineSharedTestsOwedOfLots
import E2E.OfflineOwnOwedOfLots

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles.Full (PF)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K12.AtKey (keepsKey keepsKey_same keepsKey_zero keepsKey_eleven)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) clausesOfLotsProvedPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) clausesOfLotsProvedValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) clausesOfLotsProvedDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription}

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF))
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)

/-- **owed at the four proximity tests' rows, from what is spent.** In each field the stand at every coin is
`threads_at_spent`'s. -/
theorem fourOwed_of_spent {S₁ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d (firstFamilyAt d Q)
      (fun w x => lastThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x) S₁
      (fun w x => lastSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x)) :
    FourOwed (files := Z) d where
  rangesTestOwed := rangesTestOwed_of_lots ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ Q scope hK₀ hs L
  testOnFoldedRowOwed := by
    rw [theSimulators_eq, theLetters_eq]
    exact testOnFoldedRowOwed_of_lots _ _ ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live hK₀ hs L
  testOnOmegaOwed := by
    rw [theSimulators_eq, theLetters_eq]
    exact testOnOmegaOwed_of_lots _ _ ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live hK₀ hs hN L
  ownTestOwed := ownOwed_of_spent ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ Q scope hK₀ hs L (theSimulators (files := Z) d)
    (theLetters (files := Z) d) rfl rfl rfl

/-- **THE THREE OFFLINE LINES OF ZERO KNOWLEDGE AT THE PROTOCOL's OFFLINE HONEST PROVER, FROM WHAT IS SPENT.** -/
theorem offline_clauses_of_spent {S₁ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant) (x₀ : XF)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d (firstFamilyAt d Q)
      (fun w x => lastThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x) S₁
      (fun w x => lastSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x)) :
    (∀ i r e, (offlineProver (thePartsAt Z)).ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver (thePartsAt Z))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared
        (offlineSimulatorAt d (thePartsAt Z) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))) ∧
      PrivateStopsAtMost (offlineProver (thePartsAt Z))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline 0 :=
  lines_of_four_owed live scope hd hs x₀
    (fourOwed_of_spent ℓ Nm Mg₀ tk rest Vd Z₀ B Q hd scope live hK₀ hs hN L)

/-- **The three that are asked of the rows, from what is spent.** -/
theorem offline_rows_three_of_spent {S₁ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d (firstFamilyAt d Q)
      (fun w x => lastThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x) S₁
      (fun w x => lastSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x)) :
    IsProvK Z (keyFileDescription d.source d.numbers d.later) (thePartsAt Z).book (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))
        ((thePartsAt Z).prover d) ∧
      Owed (keyFileDescription d.source d.numbers d.later) (thePartsAt Z).book
        ((cmKey Z).proverAt 0 ((thePartsAt Z).prover d)) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d)).mute (KeyRel Z) ∧
      (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d)).owns = true :=
  rows_three_of_four_owed live scope hd hs hK₀
    (fourOwed_of_spent ℓ Nm Mg₀ tk rest Vd Z₀ B Q hd scope live hK₀ hs hN L)

/-- **THE THREE OFFLINE LINES, FROM THE OFFLINE PROVER's DEBTS ON ACCEPTANCE.** -/
theorem offline_clauses_of_lots {S₁ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v)) (x₀ : XF)
    (L : TheLots (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d (firstFamilyAt d Q)
      (fun w x => lastThread ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x) S₁
      (fun w x => lastSaid ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d Q S₁ w x)) :
    (∀ i r e, (offlineProver (thePartsAt Z)).ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver (thePartsAt Z))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared
        (offlineSimulatorAt d (thePartsAt Z) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))) ∧
      PrivateStopsAtMost (offlineProver (thePartsAt Z))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline 0 :=
  offline_clauses_of_spent ℓ Nm Mg₀ tk rest Vd Z₀ B Q hd scope live hK₀ hs hN x₀
    (lotsSpent_of_lots ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ hd scope live hK₀ hN keepsKey_same
      (fun s s' h => (keepsKey_zero s s').1 h) (fun s s' h => (keepsKey_eleven s s').1 h) hC L)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.fourOwed_of_spent
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_spent
#print axioms AtPublicFiles.OfflineRows.offline_rows_three_of_spent
#print axioms AtPublicFiles.OfflineRows.offline_clauses_of_lots
