-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineClausesAtTheTerm.lean: FROM owed AT THE FOUR PROXIMITY TESTS' ROWS (`FourOwed d`, E2E/OfflineClausesOfFourOwed.lean) TO THE NAMED
VALUE OF THE OFFLINE PROVER's ARGUMENTS (`thePartsAt files`), in the two forms in which the offline half of zero knowledge is
asked; and the first of the four fields from what is spent of the offline prover's debts on acceptance.

  `rangesTestOwed_of_lots`   the field `rangesTestOwed` of `FourOwed`, at the closed terms `theSimulators d`, `theLetters d`, from
                             `LotsSpent` at the first chain's own thread: by `owed_ranges_of_lots` (E2E/OfflineRangesOwedOfLots.lean)
  `lines_of_four_owed`       the three offline lines at `offlineProver (thePartsAt files)`, at the simulator over
                             `rowsAtTheTerm d (theSimulators d) (theLetters d)`
  `rows_three_of_four_owed`  the three that are asked of the rows: `IsProvK`, `Owed` at the muted rows under the key file's relation,
                             and that every owner has a row: at `thePartsAt files`

ON THE COINS. `FourOwed` is a debt: each of its fields is asked at every input in the relation, every coin of the book and every
due list of challenges. Nothing here is a hypothesis on a run under which coins are sampled anew.

Limits. CONDITIONAL on `FourOwed`; the first field conditional on `LotsSpent`: no member of either is given here. Nothing on any
property.
-/
import E2E.OfflineClausesOfFourOwed
import E2E.OfflineLinesAtTheTerm
import E2E.OfflineRangesOwedOfLots
import E2E.OfflineObjectIsProver

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
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace)
open AtPublicFiles.FirstH (LaterFill)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost offlineSimulatorAt rangeAtFiles)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) clausesAtTheTermPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) clausesAtTheTermValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) clausesAtTheTermDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription}

section First
variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **The field `rangesTestOwed`, from the lots at the first chain's own thread.** -/
theorem rangesTestOwed_of_lots (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
    {U₃ : LastFamily Z d (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (scope : InScope Z = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (firstFamilyAt d Q) U₃ S₁ S₃) :
    OwedFirstAt (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d) (KeyRel Z)
      ((partsOfDescription (files := Z) d).prover d) rngPlace :=
  owed_ranges_of_lots ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q scope hK₀ hs L (theSimulators (files := Z) d) rfl
    (theLetters (files := Z) d) rfl rfl

end First

/-- **The three offline lines at the named value, from owed at the four tests' rows.** -/
theorem lines_of_four_owed (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (scope : InScope Z = true)
    (hd : offlineDescription Z = .ok d) (hs : KeySourced Z d.source d.numbers d.later) (x₀ : XF)
    (owed : FourOwed (files := Z) d) :
    (∀ i r e, (offlineProver (thePartsAt Z)).ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r) ∧
      ExactOutsideStops (offlineProver (thePartsAt Z))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline.cleared
        (offlineSimulatorAt d (thePartsAt Z) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))) ∧
      PrivateStopsAtMost (offlineProver (thePartsAt Z))
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y) (workAtFiles Z).offline 0 :=
  lines_at_the_term hd _ _ (offline_clauses_of_four_owed d live scope hd hs x₀ owed)

/-- **The three that are asked of the rows, at the named value.** -/
theorem rows_three_of_four_owed (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (scope : InScope Z = true)
    (hd : offlineDescription Z = .ok d) (hs : KeySourced Z d.source d.numbers d.later)
    {K₀ : KeyPub} (hK₀ : fullPub = some K₀) (owed : FourOwed (files := Z) d) :
    IsProvK Z (keyFileDescription d.source d.numbers d.later) (thePartsAt Z).book (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d))
        ((thePartsAt Z).prover d) ∧
      Owed (keyFileDescription d.source d.numbers d.later) (thePartsAt Z).book
        ((cmKey Z).proverAt 0 ((thePartsAt Z).prover d)) (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d)).mute (KeyRel Z) ∧
      (rowsAtTheTerm (files := Z) d (theSimulators (files := Z) d) (theLetters (files := Z) d)).owns = true := by
  have eP : (thePartsAt Z).prover d = (partsOfDescription (files := Z) d).prover d :=
    object_prover hd
  refine ⟨object_isProver hd hs scope _ _, ?_, owns_at d _ (offlineBook_eq hK₀) hK₀ hs scope _⟩
  rw [eP]
  exact owed_of_rest d _ _ hs scope hK₀
    (owedRest_of_rows d _ _ hs scope _
      (tenRowsOwed_of_four d _ _ (KeyRel Z) _ hs scope live
        (fourRowsOwed_of_tests d hd hs scope _ _ (fourTestsOwed_of_owed d hs scope owed))))

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.rangesTestOwed_of_lots
#print axioms AtPublicFiles.OfflineRows.lines_of_four_owed
#print axioms AtPublicFiles.OfflineRows.rows_three_of_four_owed
