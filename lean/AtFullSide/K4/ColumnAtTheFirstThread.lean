-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/ColumnAtTheFirstThread.lean: CONDITIONAL: on the head at the return, on the maker's
return at the base filling, and on ONE NAMED TEST ON PUBLIC DATA. THE FULL SIZE ALONE.

What is here. THE COLUMN hX OF THE FRAME's GATHERING ("the exchange") AT THE TWELVE MEMBERS OF THE
FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), AT THE FRAME's OWN FIRST THREAD (`firstThread`,
Honest/Thread/TheFirstThread.lean) WITH THE BASE PROVER's SCRIPT `firstScriptAt`
(AtFullSide/K1/FirstScript.lean) LAID IN: `k4_exchange_all_items`
(Honest/K4/Law/W/ExchangeAllItems.lean), which stands at a Script that is a letter, with every
hypothesis on the Script, the index, its reader, the filling's lots and the other columns paid by a
call. Nothing new is shown: a join.

  `column_hX_at_first_thread`   **at each of the eight items that the row at 28 g + 4 owes,
     `ExchangeAtS`.**

WHO PAYS WHAT. The Script lays the filling: `lays_cells`
(AtFullSide/K4/LaysCellsAtTheFirstScript.lean) · the mask row holds K4's coins:
`own_mask_row_opening` (AtFullSide/K4/SignsAtOpening.lean) at group 0, `own_mask_row_switch`
(AtFullSide/K4/SignsAtSwitches.lean) at the others · the index masks' entry:
`own_index_mask` · the index, its reader, the Script's cells: AtFullSide/K4/SignsLetters.lean · K4's
lot among the filling's: `k4_lot_at_widerFillAtCPUOWM` (Honest/K4/Law/LotThrough.lean) · `BehindS`:
`k4_behindS_at_first_thread` (Honest/K4/Law/BehindAtFirstThread.lean) · keeps leaves the statement:
`k4_keeps_the_stored_tables` (Honest/K4/Law/ClosingLinePayers.lean).

Not shown here. NO STAND OF THIS THREAD AT ANY BORDER, 0 INCLUDED, IS KNOWN TO US, SO THE STATEMENT
IS NOT KNOWN TO SPEAK AT ANY RUN: `ExchangeAtS` is an implication from the thread's stand in front
of the member and an accepting step. `enters_firstThread` (Honest/Thread/EntersFirst.lean) gives
border 0 under ready's return, okStart, the parse, `ServesAt` and `ScriptTies` at this Script, and
the last is paid nowhere; no input is known to meet `ReadyInput` at this prover, and at an input
that does not meet it the thread stands nowhere. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`: NOT AT THE
ONLINE MAKER's RETURN (`onlineFilling`, E2E/TheHonestProver.lean, is this filling read through
`OnlineProverParts.through`): the crossing is not in this file. closingReturns: that the code switch's closing
test says yes at each of its places: a test with code on public data: a hypothesis here. OF THE
EIGHT ENDS two have content ("own", wo m), two are true and empty ("planes", "join"), one is rfl
(pinW), and three say that what held in front holds behind (pin m 0, constr m .small, pinI). FIVE
THINGS ARE SPENT OUT OF THE THREAD's SENTENCE, at "own": the worths "keys", "planes" and "rider" of
the lookup on the calls and what the public item .left m says beside its test, which are owed behind
that lookup's member, and the part constr m .idn, which is open from the chain's start. Every limit
of Honest/K4/Law/W/ExchangeAllItems.lean's head holds here. That the prover's sides play the
Script's texts. Nothing on hiding. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ExchangeAllItems
import Johnson.Desc.ProofFile.Honest.K4.Law.LotThrough
import Johnson.Desc.ProofFile.Honest.K4.Law.BehindAtFirstThread
import Johnson.Desc.ProofFile.Honest.K4.Law.ClosingLinePayers
import AtFullSide.K4.SignsAtOpening
import AtFullSide.K4.SignsAtSwitches
import AtFullSide.K4.LaysCellsAtTheFirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest ProofFile.Honest.K4 ProofFile.Honest.K4.W
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread firstLetters)
open ProofFile.Honest.K1 (LocB)
open ProofFile.Honest.K4.SeatedHead (laid_at)
open ProofFile.Honest.K5 (planesAtRef_ref)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes OnBytes.Model
open OnBytes.HonestTrace (Sz)
open VerifiableInference.OnPublicFiles.Flat (indexOf)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL: on h, hA and closingReturns. **THE COLUMN hX AT K4's MEMBER OF GROUP g, AT THE
FIRST THREAD WITH THE BASE PROVER's SCRIPT.** An implication from the thread's stand in front
and an accepting step; no stand of this thread at any border is known to us. -/
theorem column_hX_at_first_thread (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (closingReturns : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop) {g : ℕ} (hg : g < 12) :
    ∀ i ∈ ((firstThread h ⟨theScript h, numbers⟩ w).row (28 * g + 4)).owes,
      ExchangeAtS (firstThread h ⟨theScript h, numbers⟩ w) Said (28 * g + 4) i := by
  obtain ⟨x, blk, Lh⟩ := laid_at h.head hg
  obtain ⟨Qp, hPG⟩ : ∃ Qp, Lot.k4PubG A.Z g = some Qp := ⟨_, k4PubG_of Lh (k4Pub_head h.head Lh)⟩
  obtain ⟨⟨M, hM, hE⟩, ho⟩ :=
    k4_lot_at_widerFillAtCPUOWM matrixInput OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G
  obtain ⟨seat, L⟩ := lays_cells h hA closingReturns (l := 2 * g) (by omega) 0
  obtain ⟨seat', L'⟩ := lays_cells h hA closingReturns (l := 2 * (g - 1)) (by omega) 0
  have Om : OwnMsgsForm (theScript h) (validInput h) 0 (maskNumAt A.Z (2 * g)) 0
      (k4MaskTxt Unit id (matrixInput.weights A.Z) k4Tokens k4LookAt Qp
        (Forest.elems (P5J.At.X A.Z).y.fo)) := by
    rcases Nat.eq_zero_or_pos g with rfl | h0
    · exact own_mask_row_opening h hA (validInput h) 0 hPG
    · exact own_mask_row_switch h hA closingReturns (validInput h) (fun _ hv => hv.1) 0 h0 hg hPG
  have Oi := own_index_mask h hA (validInput h) 0 hg hPG
  have hB := k4_behindS_at_first_thread h ⟨theScript h, numbers⟩ w Said hg
  have hKs := k4_keeps_the_stored_tables h ⟨theScript h, numbers⟩ w hg
  unfold firstThread firstLetters at hB hKs ⊢
  exact k4_exchange_all_items h.head hA (theScript h) _ _ _ _ _ 339 (validInput h) _ _ w _ _ _ rfl
    (fun _ hv => hv) Said Lh (by omega) (matrixInput.weights A.Z) hM hE ho indexOf
    trace_at_index (fun M i hi => reader_at_index A.Z M i hi)
    (fun v i _ hi => script_cells h v i hi) planesAtRef_ref (readersAt A) (fun _ => rfl) L
    (fun _ => L') hPG Om Oi (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hB
    hKs

end AtFullSide.K4.Signs

#print axioms AtFullSide.K4.Signs.column_hX_at_first_thread
